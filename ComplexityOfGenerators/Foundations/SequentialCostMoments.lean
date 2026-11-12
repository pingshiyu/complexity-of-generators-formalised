import ComplexityOfGenerators.Foundations.FreshStreamSequence

namespace ComplexityOfGenerators

private theorem two_mul_le_squares (a b : ℕ) : 2*a*b ≤ a^2+b^2 := by
  have integer : (2 : ℤ)*a*b ≤ (a : ℤ)^2+(b : ℤ)^2 := by
    nlinarith [sq_nonneg ((a : ℤ)-(b : ℤ))]
  exact_mod_cast integer

private theorem two_mul_finite_sum_le (count a : ℕ) (values : Fin count → ℕ) :
    2*a*(∑ i, values i) ≤ (∑ i, (values i)^2)+count*a^2 := by
  calc
    _ = ∑ i, 2*a*values i := Finset.mul_sum _ _ _
    _ ≤ ∑ i : Fin count, (a^2+(values i)^2) :=
      Finset.sum_le_sum (fun i _ => two_mul_le_squares a (values i))
    _ = _ := by simp [Finset.sum_add_distrib, Nat.add_comm]

/-- A finite sequence has no quadratic cross-term loss beyond its length. -/
theorem finite_sum_square_le (count : ℕ) (cost : Fin count → ℕ) :
    (∑ i, cost i)^2 ≤ count*∑ i, (cost i)^2 := by
  induction count with
  | zero => simp
  | succ count ih =>
    have remaining := ih (fun i => cost i.succ)
    have mixed := two_mul_finite_sum_le count (cost 0) (fun i => cost i.succ)
    simp only [Fin.sum_univ_succ]
    nlinarith

namespace FreshStreamSampler
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]

/-- A fixed finite sequence of fresh calls has polynomially bounded second
moment whenever each call does. Runtime may be correlated with its output. -/
theorem sequence_totalCost_secondMoment (samplers : List (FreshStreamSampler A)) (cost : A → ℕ)
    (bound : ℝ≥0∞)
    (each : ∀ sampler ∈ samplers,
      (∫⁻ stream, (cost (sampler.run stream).1 : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤ bound) :
    (∫⁻ stream, ((∑ i : Fin samplers.length, cost (((sequence samplers).run stream).1 i) : ℕ) : ℝ≥0∞)^2
      ∂fairCoinMeasure) ≤ (samplers.length : ℝ≥0∞)^2*bound := by
  have total : (samplers.map (fun sampler =>
      ∫⁻ stream, (cost (sampler.run stream).1 : ℝ≥0∞)^2 ∂fairCoinMeasure)).sum ≤
        (samplers.length : ℝ≥0∞)*bound := by
    induction samplers with
    | nil => simp
    | cons sampler rest ih =>
      have first := each sampler (by simp)
      have restBound := ih (by intro s member; exact each s (by simp [member]))
      simpa only [List.map_cons, List.sum_cons, List.length_cons, Nat.cast_add, Nat.cast_one, add_mul, one_mul,
        add_comm bound] using add_le_add first restBound
  have measurableSum : Measurable (fun stream => ∑ i : Fin samplers.length,
      (cost (((sequence samplers).run stream).1 i) : ℝ≥0∞)^2) :=
    (measurable_of_countable (fun vector : Fin samplers.length → A =>
      ∑ i, (cost (vector i) : ℝ≥0∞)^2)).comp (measurable_fst.comp (sequence samplers).measurable)
  calc
    _ ≤ ∫⁻ stream, (samplers.length : ℝ≥0∞)*∑ i : Fin samplers.length,
        (cost (((sequence samplers).run stream).1 i) : ℝ≥0∞)^2 ∂fairCoinMeasure := by
      apply lintegral_mono
      intro stream
      have natural := finite_sum_square_le samplers.length (fun i => cost (((sequence samplers).run stream).1 i))
      have casted : (((∑ i : Fin samplers.length, cost (((sequence samplers).run stream).1 i))^2 : ℕ) : ℝ≥0∞) ≤
          ((samplers.length * ∑ i : Fin samplers.length, (cost (((sequence samplers).run stream).1 i))^2 : ℕ) : ℝ≥0∞) := by
        exact_mod_cast natural
      simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_sum] using casted
    _ = (samplers.length : ℝ≥0∞)*(samplers.map (fun sampler =>
        ∫⁻ stream, (cost (sampler.run stream).1 : ℝ≥0∞)^2 ∂fairCoinMeasure)).sum := by
      rw [lintegral_const_mul _ measurableSum]
      congr 1
      exact sequence_lintegral_sum samplers (fun a => (cost a : ℝ≥0∞)^2)
    _ ≤ (samplers.length : ℝ≥0∞)*((samplers.length : ℝ≥0∞)*bound) := mul_le_mul' le_rfl total
    _ = _ := by ring

end
end FreshStreamSampler
end ComplexityOfGenerators
