import ComplexityOfGenerators.Simulation.ExactRecursive.SearchLoop

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

structure Walker (α : Type) where
  word : List α
  valid : Bool
  stopped : Bool

namespace Walker

variable {α : Type}

def afterSearch (n : ℕ) (state : Walker α) : Option (List α) → Walker α
  | some word => {state with word := word}
  | none => if state.word.length = n then {state with stopped := true} else {state with valid := false}

def answer (n : ℕ) (state : Walker α) : Option (List α) :=
  if state.valid = true ∧ state.word.length = n then some state.word else none

end Walker

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

structure WalkStored (n : ℕ) (state : Walker α) (bits : BitString) (s : Store B V) : Prop where
  input : s 11 = letters B V state.word
  index : (s 13).length = n
  random : s 17 = bits.map Symbol.bit
  empty : s 14 = []
  valid : s 29 = flagWord B V state.valid
  stopped : s 28 = flagWord B V state.stopped

namespace WalkStored

variable {B V} {n : ℕ} {state : Walker α} {bits : BitString} {s : Store B V}

theorem counter_pop (h : WalkStored B V n state bits s) :
    WalkStored B V n state bits ((Local.pop (22 : Fin 35)).eval s) := by
  rcases h with ⟨hi, hn, hr, he, hv, hs⟩
  constructor <;> simp_all [Local.eval_pop]

theorem replace_random (h : WalkStored B V n state bits s) (rest : BitString) :
    WalkStored B V n state rest (Function.update s 17 (rest.map Symbol.bit)) := by
  rcases h with ⟨hi, hn, hr, he, hv, hs⟩
  constructor <;> simp_all

theorem length_test (h : WalkStored B V n state bits s) :
    WalkStored B V n state bits ((lengthTest B V).eval s) ∧
      (lengthTest B V).eval s 30 = flagWord B V (decide (state.word.length = n)) := by
  rcases h with ⟨hi, hn, hr, he, hv, hs⟩
  constructor
  · constructor <;> simp_all [lengthTest, LengthTest.routine_eval]
  · simp [lengthTest, LengthTest.routine_eval, hi, hn, letters, flagWord]

end WalkStored

theorem searchFinish_view (n : ℕ) (state : Walker α) (label : List α) (bits : BitString)
    (selection : BoundedTrialChoice.Selection (List α)) (s : Store B V)
    (stored : SearchStored B V n state.word label bits selection s)
    (valid : s 29 = flagWord B V state.valid) (stopped : s 28 = flagWord B V state.stopped)
    (target : s 30 = flagWord B V (decide (state.word.length = n))) :
    WalkStored B V n (state.afterSearch n selection.candidate) bits ((searchFinish B V).eval s) := by
  rcases stored with ⟨hi, hl, hn, hr, he, hc, hk, hf⟩
  cases candidate : selection.candidate with
  | none =>
    by_cases size : state.word.length = n
    · constructor <;>
        simp_all [searchFinish, WordStack.Routine.branch, Walker.afterSearch, flagWord, flag_eval]
    · constructor <;>
        simp_all [searchFinish, WordStack.Routine.branch, Walker.afterSearch, flagWord, flag_eval]
  | some word =>
    constructor <;>
      simp_all [searchFinish, WordStack.Routine.branch, Walker.afterSearch, WordStack.Routine.assign_eval,
        flagWord, held] <;> rfl

theorem searchSetup_fixes_high (count : PolynomialBound) (j : Fin 35) (large : 28 ≤ j.val) :
    (searchSetup B V count).Fixes j := by
  have h12 : j ≠ 12 := by omega
  have h25 : j ≠ 25 := by omega
  have h26 : j ≠ 26 := by omega
  have h27 : j ≠ 27 := by omega
  have h23 : j ≠ 23 := by omega
  have h19 : j ≠ 19 := by omega
  have h20 : j ≠ 20 := by omega
  have h21 : j ≠ 21 := by omega
  exact (WordStack.Routine.fixes_clear 12 j h12).seq
    ((WordStack.Routine.fixes_clear 25 j h25).seq
    ((flag_fixes B V 26 j false h26).seq
    ((flag_fixes B V 27 j false h27).seq (counter_fixes B V 23 (by decide) count j h23 h19 h20 h21))))

end ComplexityOfGenerators.Simulation.ExactRecursive
