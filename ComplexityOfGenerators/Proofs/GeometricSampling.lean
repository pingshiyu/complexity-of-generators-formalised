import ComplexityOfGenerators.Foundations.Probability
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Almost-sure termination of geometric sampling

Appendix A.4 samples finite clocks and lengths by reading bits until a stop bit.
An infinite fair-coin tape almost surely has a stop bit after every offset. This
also covers a second sampling loop started at the end of the first loop: no
independence assumption about a random stopping offset is needed.
-/

namespace ComplexityOfGenerators

open MeasureTheory Filter
open scoped ENNReal Topology

def trueBlock (offset length : ℕ) : Set BitStream :=
  Set.pi (Finset.Ico offset (offset + length)) (fun _ => {true})

theorem fairCoinMeasure_trueBlock (offset length : ℕ) :
    fairCoinMeasure (trueBlock offset length) = (2 : ℝ≥0∞)⁻¹ ^ length := by
  rw [trueBlock, fairCoinMeasure, Measure.infinitePi_pi]
  · simp [PMF.uniformOfFintype_apply]
  · intro i _
    exact measurableSet_singleton _

def tailAllTrue (offset : ℕ) : Set BitStream :=
  {stream | ∀ n, offset ≤ n → stream n = true}

theorem fairCoinMeasure_tailAllTrue (offset : ℕ) : fairCoinMeasure (tailAllTrue offset) = 0 := by
  have bounds (length : ℕ) : fairCoinMeasure (tailAllTrue offset) ≤ (2 : ℝ≥0∞)⁻¹ ^ length := by
    rw [← fairCoinMeasure_trueBlock offset length]
    apply measure_mono
    intro stream member n inBlock
    exact member n (Finset.mem_Ico.mp inBlock).1
  have limit := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1)
  have zero : fairCoinMeasure (tailAllTrue offset) ≤ 0 :=
    le_of_tendsto_of_tendsto tendsto_const_nhds limit (Eventually.of_forall bounds)
  exact le_antisymm zero zero_le

/-- Fair tapes almost surely permit every finite sequence of geometric sampling
loops, even when each loop starts at an offset chosen by earlier loops. -/
theorem fairCoin_ae_stop_after_every_offset :
    ∀ᵐ stream ∂fairCoinMeasure, ∀ offset, ∃ n, offset ≤ n ∧ stream n = false := by
  rw [ae_all_iff]
  intro offset
  rw [ae_iff]
  have bad : {stream : BitStream | ¬ ∃ n, offset ≤ n ∧ stream n = false} = tailAllTrue offset := by
    ext stream
    simp only [Set.mem_ofPred_eq, tailAllTrue, not_exists, not_and]
    apply forall_congr'
    intro n
    apply imp_congr_right
    intro _
    cases stream n <;> simp
  rw [bad]
  exact fairCoinMeasure_tailAllTrue offset

/-- Binary sampling interleaves continuation flags with digit bits. The flags
still form an independent fair sequence because their positions are distinct. -/
def sampledTrueBlock (positions : ℕ → ℕ) (length : ℕ) : Set BitStream :=
  Set.pi ((Finset.range length).image positions) (fun _ => {true})

theorem fairCoinMeasure_sampledTrueBlock (positions : ℕ → ℕ)
    (distinct : Function.Injective positions) (length : ℕ) :
    fairCoinMeasure (sampledTrueBlock positions length) = (2 : ℝ≥0∞)⁻¹ ^ length := by
  rw [sampledTrueBlock, fairCoinMeasure, Measure.infinitePi_pi]
  · simp [PMF.uniformOfFintype_apply, Finset.card_image_of_injective _ distinct]
  · intro i _
    exact measurableSet_singleton _

theorem fairCoinMeasure_sampledAllTrue (positions : ℕ → ℕ)
    (distinct : Function.Injective positions) :
    fairCoinMeasure {stream : BitStream | ∀ n, stream (positions n) = true} = 0 := by
  have bounds (length : ℕ) :
      fairCoinMeasure {stream : BitStream | ∀ n, stream (positions n) = true} ≤
        (2 : ℝ≥0∞)⁻¹ ^ length := by
    rw [← fairCoinMeasure_sampledTrueBlock positions distinct length]
    apply measure_mono
    intro stream member i sampled
    obtain ⟨n, _, rfl⟩ := Finset.mem_image.mp sampled
    exact member n
  have limit := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (by norm_num : (2 : ℝ≥0∞)⁻¹ < 1)
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds limit (Eventually.of_forall bounds)) zero_le

/-- Every interleaved binary-digit sampling loop has a stop almost surely,
including loops begun at offsets selected by preceding loops. -/
theorem fairCoin_ae_stop_at_every_binary_offset :
    ∀ᵐ stream ∂fairCoinMeasure, ∀ offset, ∃ n, stream (offset + 2 * n) = false := by
  rw [ae_all_iff]
  intro offset
  rw [ae_iff]
  have bad : {stream : BitStream | ¬ ∃ n, stream (offset + 2 * n) = false} =
      {stream : BitStream | ∀ n, stream (offset + 2 * n) = true} := by
    ext stream
    simp only [Set.mem_ofPred_eq, not_exists]
    apply forall_congr'
    intro n
    cases stream (offset + 2 * n) <;> simp
  rw [bad]
  apply fairCoinMeasure_sampledAllTrue
  intro m n equal
  change offset + 2 * m = offset + 2 * n at equal
  omega

end ComplexityOfGenerators
