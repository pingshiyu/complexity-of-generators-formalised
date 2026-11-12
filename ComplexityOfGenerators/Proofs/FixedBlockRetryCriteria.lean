import ComplexityOfGenerators.Foundations.FixedBlockSelection
import ComplexityOfGenerators.Foundations.StreamSemanticsProperties

/-! Native retry controllers provide finite execution bounds for each first
successful block. These criteria transfer those actual bounds to almost-sure
productivity and expected runtime under the original fair-coin semantics. -/
namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal

namespace Machine
variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

/-- A machine accepting by a quadratic first-success deadline is productive
almost surely, and has the corresponding first-moment runtime bound. The
quadratic retry moment is proved from the fair stream, not assumed here. -/
theorem fixedBlock_retry_productivity_and_runtime (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) (constant : ℕ)
    (execution : ∀ stream,
      fixedBlock k stream (firstSuccessIndex k success stream) ∈ success →
      M.streamAcceptsBy data stream (constant * (firstSuccessIndex k success stream + 1)^2)) :
    fairCoinMeasure (M.acceptedStreams data) = 1 ∧
      M.expectedRuntime data ≤ (constant : ℝ≥0∞) * (2 / (fairBlockMeasure k success)^2) := by
  have hit := firstSuccessIndex_ae_success k positive success measurable mass
  have productive : ∀ᵐ stream ∂fairCoinMeasure, stream ∈ M.acceptedStreams data := by
    filter_upwards [hit] with stream hit
    obtain ⟨bits, word, cylinderMember, accepted⟩ := execution stream hit
    exact ⟨bits, cylinderMember, word, _, accepted⟩
  constructor
  · have null : fairCoinMeasure (M.acceptedStreams data)ᶜ = 0 := by
      exact ae_iff.mp productive
    have formula := measure_add_measure_compl (μ := fairCoinMeasure) (M.measurableSet_acceptedStreams data)
    rw [null, add_zero, measure_univ] at formula
    exact formula
  · apply fixedBlock_retry_expected_cost_le k positive success measurable (M.streamRuntime data) constant
    filter_upwards [hit] with stream hit
    have bound := M.streamRuntime_le_of_acceptsBy data (execution stream hit)
    simpa only [Nat.cast_mul, Nat.cast_pow] using bound

/-- An inverse-polynomial phase mass produces a polynomial expected bound
with no extra moment hypothesis on the source generator. -/
theorem fixedBlock_retry_runtime_of_inverse_mass (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) (constant reciprocal : ℕ)
    (lower : (reciprocal : ℝ≥0∞)⁻¹ ≤ fairBlockMeasure k success)
    (execution : ∀ stream,
      fixedBlock k stream (firstSuccessIndex k success stream) ∈ success →
      M.streamAcceptsBy data stream (constant * (firstSuccessIndex k success stream + 1)^2)) :
    M.expectedRuntime data ≤ (2 * constant * reciprocal^2 : ℕ) := by
  have inverse : (fairBlockMeasure k success)⁻¹ ≤ (reciprocal : ℝ≥0∞) := by
    simpa only [inv_inv] using ENNReal.inv_le_inv.mpr lower
  have bound := (M.fixedBlock_retry_productivity_and_runtime data k positive success measurable mass constant execution).2
  calc
    M.expectedRuntime data ≤ (constant : ℝ≥0∞) * (2 / (fairBlockMeasure k success)^2) := bound
    _ = 2 * (constant : ℝ≥0∞) * ((fairBlockMeasure k success)⁻¹)^2 := by
      rw [div_eq_mul_inv, ENNReal.inv_pow]
      ring
    _ ≤ 2 * (constant : ℝ≥0∞) * (reciprocal : ℝ≥0∞)^2 := by gcongr
    _ = _ := by simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem isGenerator_of_fixedBlock_retries (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) (constant : ℕ)
    (halting : M.HaltingTransducer data)
    (execution : ∀ stream,
      fixedBlock k stream (firstSuccessIndex k success stream) ∈ success →
      M.streamAcceptsBy data stream (constant * (firstSuccessIndex k success stream + 1)^2)) :
    M.IsGenerator data :=
  ⟨halting, Or.inl (M.fixedBlock_retry_productivity_and_runtime data k positive success measurable mass constant execution).1⟩

/-- Actual first-success output lengths inherit the bounded phase's balanced
mean. The null never-success event contributes no change to the integral. -/
theorem fixedBlock_retry_expectedLength (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) (value : (Fin k → Bool) → ℝ≥0∞)
    (valueMeasurable : Measurable value) (zero : ∀ block ∉ success, value block = 0)
    (target : ℕ) (mean : (∫⁻ block, value block ∂fairBlockMeasure k) = target * fairBlockMeasure k success)
    (length : ∀ stream, fixedBlock k stream (firstSuccessIndex k success stream) ∈ success →
      M.streamLength data stream = value (selectedBlock k success stream)) :
    M.expectedLength data = target := by
  change (∫⁻ stream, M.streamLength data stream ∂fairCoinMeasure) = target
  calc
    _ = ∫⁻ stream, value (selectedBlock k success stream) ∂fairCoinMeasure := by
      apply lintegral_congr_ae
      filter_upwards [firstSuccessIndex_ae_success k positive success measurable mass] with stream hit
      exact length stream hit
    _ = target := lintegral_selectedBlock_eq_of_phase_mean k positive success measurable mass value
      valueMeasurable zero target mean

/-- The explicit native stack compiler overhead is absorbed by a square of a
linear attempted-phase bound. This keeps the needed moment quadratic. -/
theorem retry_compiler_cost_le (ticks coefficient attempts : ℕ) (coefficientPositive : 0 < coefficient)
    (bounded : ticks ≤ coefficient * (attempts + 1)) :
    1 + (2*ticks+1)*(4*ticks+4) ≤ 25 * coefficient^2 * (attempts+1)^2 := by
  have lower : 1 ≤ coefficient * (attempts+1) := by nlinarith
  have square : ticks^2 ≤ (coefficient * (attempts+1))^2 := Nat.pow_le_pow_left bounded _
  nlinarith

end Machine
end ComplexityOfGenerators
