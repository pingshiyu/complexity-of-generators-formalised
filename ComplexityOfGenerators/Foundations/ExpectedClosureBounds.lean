import ComplexityOfGenerators.ExpectedGenerators
import ComplexityOfGenerators.Foundations.ExpectedLengthBounds
import ComplexityOfGenerators.Foundations.StreamPrefixExecution

/-!
# First-moment facts for expected-time closure constructions

These results concern the actual native evaluator on the fair-coin stream.
They justify the closure proof's zero-index treatment and its finite trials
certifying nonempty members. They do not assert the existence of a union,
concatenation, or star machine.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

namespace UniformGenerators

variable {α : Type} [Fintype α] (G : UniformGenerators α)

/-- A productive expected-length-zero member can output only the empty word. -/
theorem word_eq_nil_of_expectedLength_zero (mean : G.ExpectedLength)
    {word : List α} (member : word ∈ G.layer 0) : word = [] := by
  classical
  have integral : G.machine.expectedLength (generatorData 0) = 0 := by
    simpa using mean 0 ⟨word, member⟩
  have measurable : AEMeasurable (fun stream =>
      (G.machine.streamLength (generatorData 0) stream : ℝ≥0∞)) fairCoinMeasure :=
    ((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp
      (G.machine.measurable_streamLength (generatorData 0))).aemeasurable
  have almost : ∀ᵐ stream ∂fairCoinMeasure,
      G.machine.streamLength (generatorData 0) stream = 0 := by
    have scalar := (lintegral_eq_zero_iff' measurable).mp integral
    filter_upwards [scalar] with stream zero
    simp only [Pi.zero_apply] at zero
    exact_mod_cast zero
  have null : fairCoinMeasure {stream |
      G.machine.streamLength (generatorData 0) stream ≠ 0} = 0 := ae_iff.mp almost
  by_contra nonempty
  obtain ⟨bits, _, produces⟩ := member
  have positive : 0 < fairCoinMeasure (cylinder bits) := by
    rw [fairCoinMeasure_cylinder]
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
  have subset : cylinder bits ⊆ {stream |
      G.machine.streamLength (generatorData 0) stream ≠ 0} := by
    intro stream inCylinder zero
    have length := G.machine.streamLength_of_produces (generatorData 0)
      ⟨bits, inCylinder, produces⟩
    exact nonempty (List.length_eq_zero_iff.mp (length.symm.trans zero))
  have upper : fairCoinMeasure (cylinder bits) ≤ fairCoinMeasure {stream |
      G.machine.streamLength (generatorData 0) stream ≠ 0} := measure_mono subset
  rw [null] at upper
  exact not_lt_of_ge upper positive

end UniformGenerators

namespace Machine

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

/-- A bounded trial never needs to decide emptiness: its successful executions
are native accepting runs, and expected runtime bounds the lost probability. -/
theorem bounded_prefix_acceptance_lower_bound (p : ℝ≥0∞) (cutoff : ℕ)
    (positive : 0 < cutoff)
    (expected : M.expectedRuntime data ≤ p) :
    1 - p / (cutoff : ℝ≥0∞) ≤ fairCoinMeasure {stream | ∃ word,
      M.run data (streamPrefix stream (cutoff + 1)) cutoff = .halted (.accepted word)} := by
  have bound := measure_joint_runtime_ge_sub fairCoinMeasure Set.univ
    (M.streamRuntime data) (M.measurable_streamRuntime data).aemeasurable
    p (cutoff : ℝ≥0∞) expected (by exact_mod_cast positive.ne') (by simp)
  have subset : {stream | M.streamRuntime data stream ≤ (cutoff : ℝ≥0∞)} ⊆
      {stream | ∃ word, M.run data (streamPrefix stream (cutoff + 1)) cutoff =
        .halted (.accepted word)} := by
    intro stream runtime
    exact M.streamAcceptsBy_run_streamPrefix data (M.acceptsBy_of_streamRuntime_le data runtime)
  have lower : 1 - p / (cutoff : ℝ≥0∞) ≤
      fairCoinMeasure {stream | M.streamRuntime data stream ≤ (cutoff : ℝ≥0∞)} := by
    simpa using bound
  exact lower.trans (measure_mono subset)

/-- Doubling a positive expected-runtime bound certifies a nonempty member
with probability at least one half, using a fixed finite random block. -/
theorem bounded_prefix_acceptance_ge_half (p : ℕ) (positive : 0 < p)
    (expected : M.expectedRuntime data ≤ (p : ℝ≥0∞)) :
    (1 : ℝ≥0∞) / 2 ≤ fairCoinMeasure {stream | ∃ word,
      M.run data (streamPrefix stream (2 * p + 1)) (2 * p) = .halted (.accepted word)} := by
  have bound := M.bounded_prefix_acceptance_lower_bound data (p : ℝ≥0∞) (2 * p)
    (by omega) expected
  have ratio : (p : ℝ≥0∞) / ((2 * p : ℕ) : ℝ≥0∞) = (1 : ℝ≥0∞) / 2 := by
    rw [Nat.cast_mul, Nat.cast_ofNat]
    simp only [div_eq_mul_inv]
    rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num))]
    calc
      (p : ℝ≥0∞) * ((2 : ℝ≥0∞)⁻¹ * (p : ℝ≥0∞)⁻¹) =
          ((p : ℝ≥0∞) * (p : ℝ≥0∞)⁻¹) * (2 : ℝ≥0∞)⁻¹ := by ac_rfl
      _ = _ := by
        have nonzero : (p : ℝ≥0∞) ≠ 0 := by exact_mod_cast positive.ne'
        rw [ENNReal.mul_inv_cancel nonzero (ENNReal.natCast_ne_top p)]
  rw [ratio] at bound
  norm_num at bound ⊢
  exact bound

end Machine

end ComplexityOfGenerators
