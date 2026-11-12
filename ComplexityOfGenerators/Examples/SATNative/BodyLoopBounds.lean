import ComplexityOfGenerators.Examples.SATNative.BodyBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeBody

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem popped_represents (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active state (Function.update s 16 (s 16).tail) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  simp [Represents, word, cap, count, valid, inside, seen]

theorem popped_bound (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget (Function.update s 16 (s 16).tail) := by
  intro j
  by_cases changed : j = 16
  · subst j
    simp only [Function.update_self, List.length_tail]
    have bound := sizes 16
    omega
  · simpa [changed] using sizes j

theorem counted_properties {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    Represents capacity active (step capacity active state) ((Routine.counted 16 (bodyStep (O := O))).eval s) ∧
      stackBound budget ((Routine.counted 16 (bodyStep (O := O))).eval s) := by
  have rep := popped_represents capacity active state s represented
  have bound := popped_bound s budget sizes
  exact ⟨bodyStep_represents capacity active state _ rep,
    bodyStep_bound capacity active state _ rep budget positive bound cap count⟩

theorem iterate_properties {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) (iterations : ℕ) :
    Represents capacity active ((step capacity active)^[iterations] state)
      ((Routine.counted 16 (bodyStep (O := O))).eval^[iterations] s) ∧
    stackBound budget ((Routine.counted 16 (bodyStep (O := O))).eval^[iterations] s) := by
  induction iterations generalizing state s with
  | zero => exact ⟨represented, sizes⟩
  | succ iterations ih =>
    have one := counted_properties (O := O) capacity active state s represented budget positive sizes cap count
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih _ _ one.1 one.2

theorem bodyRoutine_bound {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    stackBound budget ((bodyRoutine (O := O)).eval s) :=
  (iterate_properties capacity active state s represented budget positive sizes cap count (s 16).length).2

/-- The complete native grammar scan uses at most one iteration per original
body symbol, each with a linear padded-record cost. -/
theorem bodyRoutine_cost {O : Type} (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    (bodyRoutine (O := O)).cost s ≤ (s 16).length * ((stepConstant + 4) * (budget + 1)) := by
  apply (Routine.loopCost_bound _ _ (s 16).length (stepConstant * (budget + 1) + 2) s ?_).trans
  · apply Nat.mul_le_mul_left
    nlinarith
  · intro i _
    have accumulated := iterate_properties (O := O) capacity active state s represented budget positive sizes cap count i
    have rep := popped_represents capacity active _ _ accumulated.1
    have bound := popped_bound _ budget accumulated.2
    have stepCost := bodyStep_cost (O := O) capacity active _ _ rep budget positive bound cap count
    change 1 + 1 + (bodyStep (O := O)).cost
      (Function.update ((Routine.counted 16 (bodyStep (O := O))).eval^[i] s) 16
        (((Routine.counted 16 (bodyStep (O := O))).eval^[i] s) 16).tail) ≤ _
    omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeBody
