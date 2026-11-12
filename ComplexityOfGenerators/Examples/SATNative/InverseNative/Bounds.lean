import ComplexityOfGenerators.Examples.SATNative.InverseNative.LoopBounds
import ComplexityOfGenerators.Examples.SATNative.InverseNative.HeaderBounds
import ComplexityOfGenerators.Examples.SATNative.InverseNative.Transform
import ComplexityOfGenerators.Examples.SATNative.SubstitutionBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack NativeBody

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] emitHeader inverseRoutine bodyTransform

/-- The actual inverse stream has the same growing-buffer resource bound as
substitution. The additional fresh variable is available under `more`. -/
theorem bodyTransform_resources {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (arguments : ℕ) (sizes : stackBound (arguments + 1) s)
    (cap : capacity ≤ arguments) (more : active + 1 ≤ capacity) (clock : (s 16).length ≤ arguments) :
    stackBound ((arguments + 2)^2) ((bodyTransform (O := O) bit).eval s) ∧
      (bodyTransform (O := O) bit).cost s ≤ NativeSubstitution.bodyBudget arguments := by
  let prepared := (emitHeader (O := O)).eval s
  have within : (s 10).length + 1 ≤ (s 4).length := by
    rw [represented.2.2.1, represented.2.1]
    simpa only [List.length_replicate] using more
  have firstBound := emitHeader_bound (O := O) s (arguments + 1) sizes within
  have firstCost := emitHeader_cost (O := O) s (arguments + 1) sizes within
  have preparedRep := emitHeader_parserFrame (O := O) capacity active state s represented
  have sameClock : prepared 16 = s 16 := emitHeader_frame (O := O) s 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have actualClock : (prepared 16).length ≤ arguments := by rw [sameClock]; exact clock
  have fits : 2 * (arguments + 1) + 2 + (prepared 16).length * (capacity + 1) ≤ (arguments + 2)^2 := by
    have growth := Nat.mul_le_mul actualClock (Nat.add_le_add_right cap 1)
    nlinarith
  have loopBound := inverseRoutine_growing_bound (O := O) bit capacity active state prepared preparedRep
    (2 * (arguments + 1) + 2) (by omega) firstBound more
  have loopCost := inverseRoutine_cost_ceiling (O := O) bit capacity active state prepared preparedRep
    (2 * (arguments + 1) + 2) ((arguments + 2)^2) (by omega) firstBound more fits
  refine ⟨?_, ?_⟩
  · unfold bodyTransform
    change stackBound ((arguments + 2)^2) ((inverseRoutine (O := O) bit).eval prepared)
    intro j
    exact (loopBound j).trans fits
  · have loopCost' : (inverseRoutine (O := O) bit).cost prepared ≤
        arguments * ((NativeBody.stepConstant + 304) * ((arguments + 2)^2 + 1)) :=
      loopCost.trans (Nat.mul_le_mul_right _ actualClock)
    unfold bodyTransform
    change (emitHeader (O := O)).cost s + 1 + (inverseRoutine (O := O) bit).cost prepared ≤ _
    unfold NativeSubstitution.bodyBudget
    omega

/-- A single polynomial controls the primitive inverse-stream cost. -/
noncomputable def bodyTransformTime : PolynomialBound := PolynomialBound.ofPolynomial
  (200 * (Polynomial.X + 2) + 1 +
    Polynomial.X * (Polynomial.C (NativeBody.stepConstant + 304) * ((Polynomial.X + 2)^2 + 1)))

theorem bodyBudget_le (arguments : ℕ) : NativeSubstitution.bodyBudget arguments ≤ bodyTransformTime arguments := by
  apply (PolynomialBound.eval_le_ofPolynomial _ arguments).trans' ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  unfold NativeSubstitution.bodyBudget
  rfl

theorem bodyTransform_bound {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (arguments : ℕ) (sizes : stackBound (arguments + 1) s)
    (cap : capacity ≤ arguments) (more : active + 1 ≤ capacity) (clock : (s 16).length ≤ arguments) :
    stackBound ((arguments + 2)^2) ((bodyTransform (O := O) bit).eval s) :=
  (bodyTransform_resources bit capacity active state s represented arguments sizes cap more clock).1

theorem bodyTransform_cost {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) (arguments : ℕ) (sizes : stackBound (arguments + 1) s)
    (cap : capacity ≤ arguments) (more : active + 1 ≤ capacity) (clock : (s 16).length ≤ arguments) :
    (bodyTransform (O := O) bit).cost s ≤ bodyTransformTime arguments :=
  (bodyTransform_resources bit capacity active state s represented arguments sizes cap more clock).2.trans (bodyBudget_le arguments)

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
