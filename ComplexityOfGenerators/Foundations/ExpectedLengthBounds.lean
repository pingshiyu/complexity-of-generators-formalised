import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

/-!
# First-moment estimates for expected-length generation

No concentration or variance assumption is used. A distribution with mean `i`
has an atom of length at least `i/2` with inverse-cubic probability. The shifted
denominator avoids exceptional treatment of length zero. The accompanying
runtime estimate is an event subtraction bound; it assumes no independence
between output length and execution time.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal BigOperators

private theorem sum_shifted_inv_sq_real (n : ℕ) :
    (∑ m ∈ Finset.range n, (((m : ℝ) + 1) ^ 2)⁻¹) ≤ 2 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
      rw [Finset.sum_range_succ]
      have telescope : (((n : ℝ) + 1) ^ 2)⁻¹ ≤
          2 / ((n : ℝ) + 1) - 2 / ((n : ℝ) + 2) := by
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg _
        apply (le_sub_iff_add_le).2
        field_simp
        nlinarith
      push_cast
      have same : (n : ℝ) + 1 + 1 = (n : ℝ) + 2 := by ring
      rw [same]
      linarith

private theorem ofReal_shifted_inv_sq (n : ℕ) :
    ENNReal.ofReal ((((n : ℝ) + 1) ^ 2)⁻¹) = (((n : ℝ≥0∞) + 1) ^ 2)⁻¹ := by
  rw [ENNReal.ofReal_inv_of_pos (by positivity), ENNReal.ofReal_pow (by positivity)]
  rw [ENNReal.ofReal_add (Nat.cast_nonneg _) (by positivity)]
  simp

/-- A convenient elementary summability bound, proved by telescoping finite sums. -/
theorem tsum_shifted_inv_sq_le_two :
    (∑' m : ℕ, (((m : ℝ≥0∞) + 1) ^ 2)⁻¹) ≤ 2 := by
  apply ENNReal.tsum_le_of_sum_range_le
  intro n
  have upper := ENNReal.ofReal_le_ofReal
    ((sum_shifted_inv_sq_real n).trans (sub_le_self _ (by positivity)))
  rw [ENNReal.ofReal_sum_of_nonneg (by intros; positivity)] at upper
  simpa only [ofReal_shifted_inv_sq, ENNReal.ofReal_ofNat] using upper

private theorem mul_inv_cube (m : ℕ) :
    ((m : ℝ≥0∞) + 1) * ((((m : ℝ≥0∞) + 1) ^ 3)⁻¹) =
      (((m : ℝ≥0∞) + 1) ^ 2)⁻¹ := by
  have hzero : (m : ℝ≥0∞) + 1 ≠ 0 := by positivity
  have htop : (m : ℝ≥0∞) + 1 ≠ ⊤ := by simp
  rw [pow_succ, ENNReal.mul_inv (Or.inr htop) (Or.inr hzero)]
  calc
    ((m : ℝ≥0∞) + 1) *
        ((((m : ℝ≥0∞) + 1) ^ 2)⁻¹ * ((m : ℝ≥0∞) + 1)⁻¹) =
        ((((m : ℝ≥0∞) + 1) * ((m : ℝ≥0∞) + 1)⁻¹) *
          (((m : ℝ≥0∞) + 1) ^ 2)⁻¹) := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel hzero htop, one_mul]

/-- The first-moment obstruction used by collision non-generability.
Only the total mass and mean are assumed; no variance bound is required. -/
theorem exists_heavy_length_atom_of_mass
    (mass : ℕ → ℝ≥0∞) (i : ℕ) (hi : 5 ≤ i)
    (total : (∑' m, mass m) ≤ 1)
    (mean : (∑' m : ℕ, (m : ℝ≥0∞) * mass m) = (i : ℝ≥0∞)) :
    ∃ m : ℕ, i ≤ 2 * m ∧
      ((((m : ℝ≥0∞) + 1) ^ 3)⁻¹) ≤ mass m := by
  by_contra absent
  have pointwise : ∀ m : ℕ,
      (2 : ℝ≥0∞) * ((m : ℝ≥0∞) * mass m) ≤
        (i : ℝ≥0∞) * mass m +
          2 * ((((m : ℝ≥0∞) + 1) ^ 2)⁻¹) := by
    intro m
    by_cases high : i ≤ 2 * m
    · have small : mass m < ((((m : ℝ≥0∞) + 1) ^ 3)⁻¹) := by
        exact lt_of_not_ge (fun bound => absent ⟨m, high, bound⟩)
      have weighted : (m : ℝ≥0∞) * mass m ≤
          ((((m : ℝ≥0∞) + 1) ^ 2)⁻¹) := by
        calc
          (m : ℝ≥0∞) * mass m ≤ ((m : ℝ≥0∞) + 1) * mass m := by gcongr; simp
          _ ≤ ((m : ℝ≥0∞) + 1) * ((((m : ℝ≥0∞) + 1) ^ 3)⁻¹) := by gcongr
          _ = _ := mul_inv_cube m
      calc
        (2 : ℝ≥0∞) * ((m : ℝ≥0∞) * mass m) ≤
            2 * ((((m : ℝ≥0∞) + 1) ^ 2)⁻¹) := by gcongr
        _ ≤ _ := le_add_of_nonneg_left (by positivity)
    · have below : (2 : ℝ≥0∞) * (m : ℝ≥0∞) ≤ (i : ℝ≥0∞) := by
        exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge high))
      calc
        (2 : ℝ≥0∞) * ((m : ℝ≥0∞) * mass m) =
            ((2 : ℝ≥0∞) * (m : ℝ≥0∞)) * mass m := (mul_assoc _ _ _).symm
        _ ≤ (i : ℝ≥0∞) * mass m := by gcongr
        _ ≤ _ := le_add_of_nonneg_right (by positivity)
  have upper : (2 : ℝ≥0∞) * (i : ℝ≥0∞) ≤ (i : ℝ≥0∞) + 4 := by
    calc
      (2 : ℝ≥0∞) * (i : ℝ≥0∞) =
          ∑' m : ℕ, (2 : ℝ≥0∞) * ((m : ℝ≥0∞) * mass m) := by
            rw [ENNReal.tsum_mul_left, mean]
      _ ≤ ∑' m : ℕ, ((i : ℝ≥0∞) * mass m +
            2 * ((((m : ℝ≥0∞) + 1) ^ 2)⁻¹)) := ENNReal.tsum_le_tsum pointwise
      _ = (i : ℝ≥0∞) * (∑' m, mass m) +
          2 * (∑' m : ℕ, ((((m : ℝ≥0∞) + 1) ^ 2)⁻¹)) := by
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left]
      _ ≤ (i : ℝ≥0∞) * 1 + 2 * 2 := by
        gcongr
        exact tsum_shifted_inv_sq_le_two
      _ = _ := by norm_num
  have contradiction : 2 * i ≤ i + 4 := by exact_mod_cast upper
  omega

/-- Heavy atoms occur at unbounded lengths even when a family is required to
have the stated mean only at sufficiently large indices. -/
theorem unbounded_heavy_length_atoms_of_mass
    (mass : ℕ → ℕ → ℝ≥0∞) (firstIndex : ℕ)
    (total : ∀ i, firstIndex ≤ i → (∑' m, mass i m) ≤ 1)
    (mean : ∀ i, firstIndex ≤ i →
      (∑' m : ℕ, (m : ℝ≥0∞) * mass i m) = (i : ℝ≥0∞)) :
    ∀ bound : ℕ, ∃ i m : ℕ, firstIndex ≤ i ∧ bound ≤ m ∧ i ≤ 2 * m ∧
      ((((m : ℝ≥0∞) + 1) ^ 3)⁻¹) ≤ mass i m := by
  intro bound
  let i := max firstIndex (max 5 (2 * bound))
  have first : firstIndex ≤ i := le_max_left _ _
  have large : 5 ≤ i := (le_max_left _ _).trans (le_max_right _ _)
  have index_bound : 2 * bound ≤ i := (le_max_right _ _).trans (le_max_right _ _)
  obtain ⟨m, hm, heavy⟩ :=
    exists_heavy_length_atom_of_mass (mass i) i large (total i first) (mean i first)
  exact ⟨i, m, first, by omega, hm, heavy⟩

/-- The expectation of a measurable natural-valued random variable is its
countable first moment. This is the bridge from the integral definition. -/
theorem lintegral_nat_eq_tsum_atoms {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (length : Ω → ℕ) (measurable : Measurable length) :
    (∫⁻ s, (length s : ℝ≥0∞) ∂μ) =
      ∑' m : ℕ, (m : ℝ≥0∞) * μ {s | length s = m} := by
  calc
    (∫⁻ s, (length s : ℝ≥0∞) ∂μ) =
        ∫⁻ m : ℕ, (m : ℝ≥0∞) ∂Measure.map length μ :=
      (lintegral_map (measurable_of_countable _) measurable).symm
    _ = ∑' m : ℕ, (m : ℝ≥0∞) * (Measure.map length μ) {m} :=
      lintegral_countable' _
    _ = _ := by
      apply tsum_congr
      intro m
      rw [Measure.map_apply measurable (measurableSet_singleton m)]
      rfl

/-- Integral form of the first-moment estimate on a probability space. -/
theorem tsum_nat_atom_measures_eq_one {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (length : Ω → ℕ) (measurable : Measurable length) :
    (∑' m : ℕ, μ {s | length s = m}) = 1 := by
  have total := measure_iUnion (μ := μ)
    (f := fun m : ℕ => {s | length s = m})
    (fun a b different => by
      change Disjoint {s | length s = a} {s | length s = b}
      rw [Set.disjoint_left]
      intro s ha hb
      exact different (ha.symm.trans hb))
    (fun m => measurable (measurableSet_singleton m))
  have whole : (⋃ m : ℕ, {s | length s = m}) = Set.univ := by ext s; simp
  simpa [whole] using total.symm

/-- Integral form of the first-moment estimate on a probability space. -/
theorem exists_heavy_length_atom {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (length : Ω → ℕ) (measurable : Measurable length)
    (i : ℕ) (hi : 5 ≤ i)
    (mean : (∫⁻ s, (length s : ℝ≥0∞) ∂μ) = (i : ℝ≥0∞)) :
    ∃ m : ℕ, i ≤ 2 * m ∧
      ((((m : ℝ≥0∞) + 1) ^ 3)⁻¹) ≤ μ {s | length s = m} := by
  apply exists_heavy_length_atom_of_mass (fun m => μ {s | length s = m}) i hi
  · exact (tsum_nat_atom_measures_eq_one μ length measurable).le
  · rwa [← lintegral_nat_eq_tsum_atoms μ length measurable]

/-- Markov bounds the lost part of an arbitrary event. Output length and runtime
may be dependent; no independence hypothesis is present. -/
theorem measure_le_joint_runtime_add {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (event : Set Ω) (runtime : Ω → ℝ≥0∞)
    (measurable : AEMeasurable runtime μ) (p cutoff : ℝ≥0∞)
    (expected : (∫⁻ s, runtime s ∂μ) ≤ p)
    (cutoff_pos : cutoff ≠ 0) (cutoff_finite : cutoff ≠ ⊤) :
    μ event ≤ μ (event ∩ {s | runtime s ≤ cutoff}) + p / cutoff := by
  have markov := (meas_ge_le_lintegral_div measurable cutoff_pos cutoff_finite).trans
    (ENNReal.div_le_div_right expected cutoff)
  calc
    μ event ≤ μ (event ∩ {s | runtime s ≤ cutoff}) +
        μ (event \ {s | runtime s ≤ cutoff}) := measure_le_inter_add_sdiff _ _ _
    _ ≤ μ (event ∩ {s | runtime s ≤ cutoff}) + μ {s | cutoff ≤ runtime s} := by
      gcongr
      intro s hs
      exact (lt_of_not_ge (show ¬ runtime s ≤ cutoff from hs.2)).le
    _ ≤ _ := add_le_add le_rfl markov

/-- Subtractive form of the joint-event runtime estimate. -/
theorem measure_joint_runtime_ge_sub {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (event : Set Ω) (runtime : Ω → ℝ≥0∞)
    (measurable : AEMeasurable runtime μ) (p cutoff : ℝ≥0∞)
    (expected : (∫⁻ s, runtime s ∂μ) ≤ p)
    (cutoff_pos : cutoff ≠ 0) (cutoff_finite : cutoff ≠ ⊤) :
    μ event - p / cutoff ≤ μ (event ∩ {s | runtime s ≤ cutoff}) := by
  apply (tsub_le_iff_right).2
  simpa only [add_comm] using
    measure_le_joint_runtime_add μ event runtime measurable p cutoff expected cutoff_pos cutoff_finite

/-- If the runtime cutoff loses at most half the guaranteed event mass, at least
half survives. This form is convenient when choosing a polynomial cutoff. -/
theorem measure_joint_runtime_ge_half {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (event : Set Ω) (runtime : Ω → ℝ≥0∞)
    (measurable : AEMeasurable runtime μ) (p cutoff δ : ℝ≥0∞)
    (expected : (∫⁻ s, runtime s ∂μ) ≤ p)
    (cutoff_pos : cutoff ≠ 0) (cutoff_finite : cutoff ≠ ⊤)
    (mass : δ ≤ μ event) (finite : δ ≠ ⊤) (loss : p / cutoff ≤ δ / 2) :
    δ / 2 ≤ μ (event ∩ {s | runtime s ≤ cutoff}) := by
  calc
    δ / 2 = δ - δ / 2 := (ENNReal.sub_half finite).symm
    _ ≤ μ event - p / cutoff := tsub_le_tsub mass loss
    _ ≤ _ := measure_joint_runtime_ge_sub μ event runtime measurable p cutoff expected
      cutoff_pos cutoff_finite

end ComplexityOfGenerators
