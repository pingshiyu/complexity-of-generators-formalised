import ComplexityOfGenerators.Foundations.FreshStreamSamplers

/-! Sequential fresh calls preserve additive means. Their squared total
primitive cost is controlled by the sum of the individual second moments,
without requiring independence between runtime and output length. -/
namespace ComplexityOfGenerators.FreshStreamSampler
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {A : Type} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]

noncomputable def sequence : (samplers : List (FreshStreamSampler A)) → FreshStreamSampler (Fin samplers.length → A)
  | [] => pure (fun i => Fin.elim0 i)
  | sampler :: rest => sampler.bind (fun a => (sequence rest).map (Fin.cons (α := fun _ => A) a) (measurable_of_countable _))

/-- Means add for any finite list of concrete fresh samplers. The result is
about the sequential stream execution, rather than an independently supplied
product of random sources. -/
theorem sequence_lintegral_sum (samplers : List (FreshStreamSampler A)) (value : A → ℝ≥0∞) :
    (∫⁻ stream, ∑ i : Fin samplers.length, value (((sequence samplers).run stream).1 i) ∂fairCoinMeasure) =
      (samplers.map (fun sampler => ∫⁻ stream, value (sampler.run stream).1 ∂fairCoinMeasure)).sum := by
  induction samplers with
  | nil => simp [sequence, pure]
  | cons sampler rest ih =>
    change (∫⁻ stream, (fun vector : Fin (rest.length+1) → A => ∑ i, value (vector i))
      ((sampler.bind (fun a => (sequence rest).map (Fin.cons (α := fun _ => A) a) (measurable_of_countable _))).run stream).1
        ∂fairCoinMeasure) = _
    have first := lintegral_bind sampler
      (fun a => (sequence rest).map (Fin.cons (n := rest.length) (α := fun _ => A) a) (measurable_of_countable _))
      (fun vector : Fin (rest.length+1) → A => ∑ i, value (vector i)) (measurable_of_countable _)
    refine first.trans ?_
    have inner (a : A) :
        (∫⁻ future, ∑ i : Fin (rest.length+1), value ((((sequence rest).map (Fin.cons (α := fun _ => A) a) (measurable_of_countable _)).run future).1 i)
          ∂fairCoinMeasure) = value a + ∫⁻ future, ∑ i : Fin rest.length, value (((sequence rest).run future).1 i) ∂fairCoinMeasure := by
      simp only [map, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
      rw [lintegral_add_left measurable_const]
      simp
    simp_rw [inner]
    rw [lintegral_add_left (measurable_of_countable _), lintegral_const, measure_univ, mul_one, distribution]
    have sourceMeasurable : Measurable (fun stream => (sampler.run stream).1) := measurable_fst.comp sampler.measurable
    rw [lintegral_map (measurable_of_countable value) sourceMeasurable, ih]
    rfl

end
end ComplexityOfGenerators.FreshStreamSampler
