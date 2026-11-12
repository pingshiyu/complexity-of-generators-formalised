import ComplexityOfGenerators.Examples.SATNative.EvaluationBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem counted_properties {O : Type} (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (s : Store) (represented : Represents capacity active certificate state s) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    Represents capacity active certificate (step capacity active certificate state)
      ((Routine.counted 16 (evaluationStep (O := O))).eval s) ∧
      stackBound budget ((Routine.counted 16 (evaluationStep (O := O))).eval s) := by
  have rep := NativeEvaluation.popped_represents capacity active certificate state s represented
  have bound := NativeBody.popped_bound s budget sizes
  exact ⟨evaluationStep_represents capacity active certificate state _ rep,
    evaluationStep_bound capacity active certificate state _ rep budget positive bound cap count⟩

theorem iterate_properties {O : Type} (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (s : Store) (represented : Represents capacity active certificate state s) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) (iterations : ℕ) :
    Represents capacity active certificate ((step capacity active certificate)^[iterations] state)
      ((Routine.counted 16 (evaluationStep (O := O))).eval^[iterations] s) ∧
    stackBound budget ((Routine.counted 16 (evaluationStep (O := O))).eval^[iterations] s) := by
  induction iterations generalizing state s with
  | zero => exact ⟨represented, sizes⟩
  | succ iterations ih =>
    have one := counted_properties (O := O) capacity active certificate state s represented budget positive sizes cap count
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
    exact ih _ _ one.1 one.2

theorem evaluationRoutine_bound {O : Type} (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (s : Store) (represented : Represents capacity active certificate state s) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    stackBound budget ((evaluationRoutine (O := O)).eval s) :=
  (iterate_properties capacity active certificate state s represented budget positive sizes cap count (s 16).length).2

theorem evaluationRoutine_cost {O : Type} (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (s : Store) (represented : Represents capacity active certificate state s) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    (evaluationRoutine (O := O)).cost s ≤ (s 16).length * ((stepConstant + 4) * (budget + 1)) := by
  apply (Routine.loopCost_bound _ _ (s 16).length (stepConstant * (budget + 1) + 2) s ?_).trans
  · apply Nat.mul_le_mul_left
    nlinarith
  · intro i _
    have accumulated := iterate_properties (O := O) capacity active certificate state s represented budget positive sizes cap count i
    have rep := NativeEvaluation.popped_represents capacity active certificate _ _ accumulated.1
    have bound := NativeBody.popped_bound _ budget accumulated.2
    have stepCost := evaluationStep_cost (O := O) capacity active certificate _ _ rep budget positive bound cap count
    change 1 + 1 + (evaluationStep (O := O)).cost
      (Function.update ((Routine.counted 16 (evaluationStep (O := O))).eval^[i] s) 16
        (((Routine.counted 16 (evaluationStep (O := O))).eval^[i] s) 16).tail) ≤ _
    omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
