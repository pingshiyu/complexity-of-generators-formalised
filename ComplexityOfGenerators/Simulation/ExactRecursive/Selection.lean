import ComplexityOfGenerators.Simulation.ExactRecursive.Program
import ComplexityOfGenerators.Proofs.IterativeTrialChoice

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

def letters (word : List α) : List (Cell B V) := word.map Symbol.letter

def held : Option (List α) → List (Cell B V)
  | none => []
  | some word => letters B V word

def flagWord (b : Bool) : List (Cell B V) := if b then [.unit] else []

def SelectionStored (s : Store B V) (selection : BoundedTrialChoice.Selection (List α)) : Prop :=
  s 25 = held B V selection.candidate ∧ s 26 = flagWord B V selection.locked ∧
    s 27 = flagWord B V selection.candidate.isSome

def positiveResult (label : List α) (status : Source.Status (Fin V.states)) (output : List α) : Option (List α) :=
  if label = [] then none else match status with | .accepted => some output.reverse | _ => none

theorem takeOutput_eval (dst : Fin 35) (different : (10 : Fin 35) ≠ dst) (map : Cell B V → Cell B V)
    (s : Store B V) :
    (takeOutput B V dst different map).eval s =
      Function.update (Function.update s 10 []) dst ((s 10).reverse.map map) := by
  funext j
  by_cases hd : j = dst <;> by_cases ho : j = 10 <;>
    simp_all [takeOutput, WordStack.Routine.seq, WordStack.Routine.clear,
      WordStack.Routine.transfer, Function.update_apply, different.symm]

theorem flag_eval (reg : Fin 35) (b : Bool) (s : Store B V) :
    (flag B V reg b).eval s = Function.update s reg (flagWord B V b) := by
  cases b <;> simp [flag, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.ofLocal,
    WordStack.Routine.skip, Local.eval, Local.push, Action.apply, flagWord, Function.update_idem]

theorem offer_stored (coin : Bool) (s : Store B V) (selection : BoundedTrialChoice.Selection (List α))
    (label output : List α) (status : Source.Status (Fin V.states))
    (stored : SelectionStored B V s selection) (word : s 12 = letters B V label)
    (state : s 0 = [.inverse (.state status)])
    (result : s 10 = output.map (fun a => Symbol.inverse (Source.Cell.output a))) :
    SelectionStored B V ((offer B V coin).eval s)
      (selection.offer (positiveResult V label status output) coin) := by
  rcases stored with ⟨hc, hl, hf⟩
  by_cases locked : selection.locked = true
  · have unchanged : (offer B V coin).eval s = s := by
      simp only [offer, WordStack.Routine.branch, hl, flagWord, locked, ite_true,
        List.head?_cons, Option.isSome_some, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval]
    rw [unchanged]
    simpa only [SelectionStored, BoundedTrialChoice.Selection.offer, locked, ite_true] using And.intro hc (And.intro hl hf)
  · have unlocked : selection.locked = false := Bool.eq_false_iff.mpr locked
    by_cases empty : label = []
    · have unchanged : (offer B V coin).eval s = s := by
        simp only [offer, WordStack.Routine.branch, hl, flagWord, unlocked, Bool.false_eq_true, ite_false,
          List.head?_nil, Option.isSome_none, word, empty, letters, List.map_nil, Option.isNone_none,
          ite_true, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval]
      rw [unchanged]
      simpa only [SelectionStored, BoundedTrialChoice.Selection.offer, unlocked, Bool.false_eq_true, ite_false,
        positiveResult, empty, ite_true] using And.intro hc (And.intro hl hf)
    · cases label_eq : label with
      | nil => exact (empty label_eq).elim
      | cons a rest =>
        have observation : (s 12).head?.isNone = false := by simp only [word, label_eq, letters, List.map_cons,
          List.head?_cons, Option.isNone_some]
        cases status with
        | live q | rejected | exhausted =>
          have unchanged : (offer B V coin).eval s = s := by
            simp only [offer, WordStack.Routine.branch, hl, flagWord, unlocked, Bool.false_eq_true, ite_false,
              List.head?_nil, Option.isSome_none, observation, state, List.head?_cons,
              WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval]
          rw [unchanged]
          simpa only [SelectionStored, BoundedTrialChoice.Selection.offer, unlocked, Bool.false_eq_true, ite_false,
            positiveResult, label_eq, List.cons_ne_nil] using And.intro hc (And.intro hl hf)
        | accepted =>
          simp only [offer, WordStack.Routine.branch, hl, flagWord, unlocked, Bool.false_eq_true, ite_false,
            List.head?_nil, Option.isSome_none, observation, state, List.head?_cons,
            BoundedTrialChoice.Selection.offer, positiveResult, label_eq, List.cons_ne_nil]
          cases coin <;>
            simp [SelectionStored, WordStack.Routine.seq, takeOutput_eval, flag_eval,
              WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, held, flagWord, letters,
              result, hl, unlocked, inverseOutput, List.map_map, Function.comp_def]

theorem coin_eval (no yes : Controller B V) (s : Store B V) (bit : Bool) (rest : BitString)
    (random : s 17 = (bit :: rest).map Symbol.bit) :
    (coin B V no yes).eval s = (if bit then yes else no).eval
      (Function.update s 17 (rest.map Symbol.bit)) := by
  cases bit <;> simp [coin, WordStack.Routine.branch, WordStack.Routine.seq,
    WordStack.Routine.ofLocal, Local.eval_pop, random]

theorem increment_word (first : α) (s : Store B V) (word : List α) (encoded : s 12 = letters B V word) :
    (increment B V first).eval s 12 = letters B V (Shortlex.next first word) := by
  have equal : WordCounter.successor first CyclicGenerator.nextLetter word = Shortlex.next first word := by
    clear encoded
    induction word with
    | nil => rfl
    | cons a rest ih =>
      cases h : CyclicGenerator.nextLetter a <;>
        simp [WordCounter.successor, Shortlex.next, h, ih]
  have mapped := WordCounter.successor_map (fun a : α => (Symbol.letter a : Cell B V)) first
    CyclicGenerator.nextLetter (nextLetter B V) (fun _ => rfl) word
  simp only [increment, WordCounter.routine_eval, Function.update_self, encoded, letters]
  exact mapped.trans (congrArg (List.map Symbol.letter) equal)

theorem increment_selection (first : α) (s : Store B V) (selection : BoundedTrialChoice.Selection (List α))
    (stored : SelectionStored B V s selection) : SelectionStored B V ((increment B V first).eval s) selection := by
  simpa only [SelectionStored, increment_fixes B V first 25 (by decide) (by decide) s,
    increment_fixes B V first 26 (by decide) (by decide) s,
    increment_fixes B V first 27 (by decide) (by decide) s] using stored

end ComplexityOfGenerators.Simulation.ExactRecursive
