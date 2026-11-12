import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Value
import ComplexityOfGenerators.Examples.HAMPATHNative.Cell
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def literalCode : List Symbol → Local Symbol 64
  | [] => .read 43 fun head => if head.isSome then Local.pop 44 else .skip
  | symbol :: rest => .read 43 fun head => if head = some symbol then
      (Local.pop 43).seq (literalCode rest) else Local.pop 44

theorem literalCode_flag (literal : List Symbol) (s : Local.Store Symbol 64) :
    (literalCode literal).eval s 44 = if s 43 = literal then s 44 else (s 44).tail := by
  induction literal generalizing s with
  | nil => cases word : s 43 <;> simp [literalCode, Local.eval, Local.pop, Action.apply, word]
  | cons symbol rest ih =>
      cases word : s 43 with
      | nil => simp [literalCode, Local.eval, Local.pop, Action.apply, word]
      | cons head tail =>
          by_cases same : head = symbol
          · subst head
            simp only [literalCode, Local.eval_read, word, List.head?_cons, ite_true, Local.eval_seq,
              Local.eval_pop, ih, Function.update_self, Function.update_of_ne (by decide : (44 : Fin 64) ≠ 43)]
            simp
          · simp [literalCode, Local.eval, Local.pop, Action.apply, word, same]

theorem literalCode_frame (literal : List Symbol) (s : Local.Store Symbol 64) (j : Fin 64)
    (word : j ≠ 43) (result : j ≠ 44) : (literalCode literal).eval s j = s j := by
  induction literal generalizing s with
  | nil => simp only [literalCode, Local.eval_read]; split <;> simp [Local.eval, Local.pop, Action.apply, result]
  | cons symbol rest ih =>
      simp only [literalCode, Local.eval_read]
      split
      · simp [Local.eval_seq, ih, Local.eval_pop, word]
      · simp [Local.eval_pop, result]

theorem literalCode_ticks (literal : List Symbol) (s : Local.Store Symbol 64) :
    (literalCode literal).ticks s ≤ 3 * literal.length + 2 := by
  induction literal generalizing s with
  | nil => simp only [literalCode, Local.ticks, List.length_nil]; split <;> simp [Local.ticks, Local.pop]
  | cons symbol rest ih =>
      simp only [literalCode, Local.ticks, List.length_cons]
      split
      · have := ih ((Local.pop 43).eval s)
        change 1 + (1 + 1 + (literalCode rest).ticks ((Local.pop 43).eval s)) ≤ _
        omega
      · simp [Local.ticks, Local.pop] <;> omega

def baseTest : Routine Symbol Unit 64 :=
  (Routine.assign 32 43 40 (by decide) (by decide) (by decide) id).seq
    ((Routine.clear 44).seq ((Routine.ofLocal (Local.push 44 (.bit true))).seq (Routine.ofLocal (literalCode baseWord))))

theorem baseTest_flag (s : Local.Store Symbol 64) :
    baseTest.eval s 44 = flag (decide (s 32 = baseWord)) := by
  simp [baseTest, Routine.seq, Routine.assign_eval, Routine.clear, Routine.ofLocal, Local.eval_push,
    literalCode_flag, flag]

theorem baseTest_frame (s : Local.Store Symbol 64) (j : Fin 64)
    (a : j ≠ 40) (b : j ≠ 43) (c : j ≠ 44) : baseTest.eval s j = s j := by
  simp [baseTest, Routine.seq, Routine.assign_eval, Routine.clear, Routine.ofLocal,
    literalCode_frame _ _ j b c, Local.eval_push, a, b, c]

theorem baseWord_length : baseWord.length = 5 := by decide

theorem baseTest_bound (s : Local.Store Symbol 64) (budget : ℕ) (positive : 1 ≤ budget)
    (sizes : StoreBound s budget) : StoreBound (baseTest.eval s) budget ∧ baseTest.cost s ≤ 30 * budget + 30 := by
  have assigned := sizes.assign (O := Unit) 32 43 40 (by decide) (by decide) (by decide) id
  let a := (Routine.assign (O := Unit) 32 43 40 (by decide) (by decide) (by decide) id).eval s
  let b := Function.update (Function.update a 44 []) 44 [Symbol.bit true]
  have bBound : StoreBound b budget := (assigned.clear 44).update 44 _ (by simpa using positive)
  have localBound : StoreBound ((literalCode baseWord).eval b) budget := by
    intro j
    by_cases result : j = 44
    · subst j
      rw [literalCode_flag]
      split
      · exact bBound 44
      · simp only [List.length_tail]; have := bBound 44; omega
    · by_cases word : j = 43
      · subst j
        have remaining (literal : List Symbol) (t : Local.Store Symbol 64) :
            ((literalCode literal).eval t 43).length ≤ (t 43).length := by
          induction literal generalizing t with
          | nil => simp only [literalCode, Local.eval_read]; split <;> simp [Local.eval, Local.pop, Action.apply]
          | cons head rest ih =>
              simp only [literalCode, Local.eval_read]
              split
              · exact (ih _).trans (by simp [Local.eval_pop, List.length_tail] <;> omega)
              · simp [Local.eval_pop]
        exact (remaining _ _).trans (bBound 43)
      · rw [literalCode_frame _ _ j word result]
        exact bBound j
  refine ⟨localBound, ?_⟩
  have ticks := literalCode_ticks baseWord b
  rw [baseWord_length] at ticks
  have x := sizes 43
  have y := sizes 40
  have z := sizes 32
  have q : (a 44).length ≤ budget := assigned 44
  change (Routine.assign (O := Unit) 32 43 40 (by decide) (by decide) (by decide) id).cost s + 1 +
    (3 * (a 44).length + 1 + (1 + 1 + (literalCode baseWord).ticks b)) ≤ _
  rw [Routine.assign_cost]
  omega

theorem baseTest_randomFree : Command.RandomFree baseTest.command := by simp [baseTest]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
