import ComplexityOfGenerators.Examples.SATNative.SubstitutionStepBounds
import ComplexityOfGenerators.Examples.SATNative.SubstitutionComplete

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] substitutionStep substitutionRoutine

theorem counted_properties {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    Represents capacity active (NativeBody.step capacity active state) ((countedStep (O := O) bit).eval s) ∧
      stackBound (budget + capacity + 1) ((countedStep (O := O) bit).eval s) := by
  have rep := NativeBody.popped_represents capacity active state s represented
  have bound := NativeBody.popped_bound s budget sizes
  exact ⟨substitutionStep_represents (O := O) bit capacity active state _ rep,
    substitutionStep_bound (O := O) bit capacity active state _ rep budget positive bound cap count⟩

theorem iterate_properties {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) (iterations : ℕ) :
    Represents capacity active ((NativeBody.step capacity active)^[iterations] state)
      ((countedStep (O := O) bit).eval^[iterations] s) ∧
    stackBound (budget + iterations * (capacity + 1)) ((countedStep (O := O) bit).eval^[iterations] s) := by
  induction iterations generalizing state s budget with
  | zero => simpa using And.intro represented sizes
  | succ iterations ih =>
    have one := counted_properties (O := O) bit capacity active state s represented budget positive sizes cap count
    have remaining := ih _ _ one.1 (budget + capacity + 1) (by omega) one.2 (by omega) (by omega)
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    refine ⟨remaining.1, ?_⟩
    convert remaining.2 using 1 <;> nlinarith

theorem substitutionRoutine_growing_bound {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    stackBound (budget + (s 16).length * (capacity + 1)) ((substitutionRoutine (O := O) bit).eval s) := by
  unfold substitutionRoutine
  exact (iterate_properties bit capacity active state s represented budget positive sizes cap count (s 16).length).2

/-- A fixed ceiling bounds every growing intermediate store. The resulting
primitive cost is linear in the clock and in this proved store ceiling. -/
theorem substitutionRoutine_cost_ceiling {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (budget : ℕ) (positive : 0 < budget)
    (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget)
    (ceiling : ℕ) (fits : budget + (s 16).length * (capacity + 1) ≤ ceiling) :
    (substitutionRoutine (O := O) bit).cost s ≤
      (s 16).length * ((NativeBody.stepConstant + 304) * (ceiling + 1)) := by
  unfold substitutionRoutine
  change Routine.loopCost _ _ (s 16).length s ≤ _
  apply (Routine.loopCost_bound _ _ (s 16).length ((NativeBody.stepConstant + 300) * (ceiling + 1) + 2) s ?_).trans
  · apply Nat.mul_le_mul_left
    nlinarith
  · intro i inside
    have current := iterate_properties (O := O) bit capacity active state s represented budget positive sizes cap count i
    have upper : budget + i * (capacity + 1) ≤ ceiling := by
      exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.le_of_lt inside)) _).trans fits
    have bounded : stackBound ceiling ((countedStep (O := O) bit).eval^[i] s) := by
      intro j
      exact (current.2 j).trans upper
    have rep := NativeBody.popped_represents capacity active _ _ current.1
    have popped := NativeBody.popped_bound _ ceiling bounded
    have stepCost := substitutionStep_cost (O := O) bit capacity active _ _ rep ceiling (by omega) popped (by omega) (by omega)
    change 1 + 1 + (substitutionStep (O := O) bit).cost
      (Function.update ((countedStep (O := O) bit).eval^[i] s) 16
        (((countedStep (O := O) bit).eval^[i] s) 16).tail) ≤ _
    omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
