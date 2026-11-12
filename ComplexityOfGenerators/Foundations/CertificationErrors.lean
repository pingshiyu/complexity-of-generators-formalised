import ComplexityOfGenerators.Foundations.IndexwiseCertification

/-! Summable error budgets for one native bounded test at each needed index. -/
namespace ComplexityOfGenerators.IndexwiseCertification
open scoped ENNReal
noncomputable section

private def realError (n : ℕ) : ℝ := 1/(16*((n : ℝ)+1)^2)
private def reciprocal (n : ℕ) : ℝ := 1/(8*((n : ℝ)+1))

private theorem reciprocal_gap (n : ℕ) :
    reciprocal n-reciprocal (n+1) = 1/(8*((n : ℝ)+1)*((n : ℝ)+2)) := by
  have first : (n : ℝ)+1 ≠ 0 := ne_of_gt (by positivity)
  have second : (n : ℝ)+2 ≠ 0 := ne_of_gt (by positivity)
  simp only [reciprocal, Nat.cast_add, Nat.cast_one]
  field_simp
  <;> ring

private theorem realError_le_gap (n : ℕ) : realError n ≤ reciprocal n-reciprocal (n+1) := by
  rw [reciprocal_gap]
  unfold realError
  apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
  nlinarith [Nat.cast_nonneg (α := ℝ) n]

private theorem realError_sum_le (count : ℕ) :
    (∑ n ∈ Finset.range count, realError n) ≤ (1 : ℝ)/8 := by
  have gapSum := Finset.sum_range_sub' reciprocal count
  calc
    _ ≤ ∑ n ∈ Finset.range count, (reciprocal n-reciprocal (n+1)) :=
      Finset.sum_le_sum (fun n _ => realError_le_gap n)
    _ = reciprocal 0-reciprocal count := gapSum
    _ ≤ reciprocal 0 := sub_le_self _ (by unfold reciprocal; positivity)
    _ = (1 : ℝ)/8 := by norm_num [reciprocal]

private theorem ofReal_realError (n : ℕ) :
    ENNReal.ofReal (realError n) = ((16*(n+1)^2 : ℕ) : ℝ≥0∞)⁻¹ := by
  unfold realError
  rw [one_div, ENNReal.ofReal_inv_of_pos (by positivity)]
  have denominator : 16*((n : ℝ)+1)^2 = ((16*(n+1)^2 : ℕ) : ℝ) := by
    simp only [Nat.cast_mul, Nat.cast_pow, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat]
  rw [denominator, ENNReal.ofReal_natCast]

/-- The complete finite error budget is bounded uniformly in the outer
index, using only polynomially many bits and steps at each source index. -/
theorem total_failure_budget (count : ℕ) :
    (∑ n ∈ Finset.range count, ((16*(n+1)^2 : ℕ) : ℝ≥0∞)⁻¹) ≤ (1 : ℝ≥0∞)/8 := by
  calc
    _ = ∑ n ∈ Finset.range count, ENNReal.ofReal (realError n) := by simp_rw [ofReal_realError]
    _ = ENNReal.ofReal (∑ n ∈ Finset.range count, realError n) :=
      (ENNReal.ofReal_sum_of_nonneg (by intro n _; unfold realError; positivity)).symm
    _ ≤ ENNReal.ofReal ((1 : ℝ)/8) := ENNReal.ofReal_le_ofReal (realError_sum_le count)
    _ = _ := by rw [ENNReal.ofReal_div_of_pos (by norm_num)]; norm_num

end

end ComplexityOfGenerators.IndexwiseCertification
