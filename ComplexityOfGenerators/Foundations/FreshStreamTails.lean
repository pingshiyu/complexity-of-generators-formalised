import ComplexityOfGenerators.Foundations.FreshStreamSamplers

namespace ComplexityOfGenerators.FreshStreamSampler
open MeasureTheory
variable {A : Type} [MeasurableSpace A] (sampler : FreshStreamSampler A)
set_option backward.isDefEq.respectTransparency false

/-- A measurable predicate holds almost surely for a returned value exactly
when it holds for the actual stream execution that produces that value. -/
theorem distribution_ae_iff (predicate : A → Prop) (measurable : MeasurableSet {a | predicate a}) :
    (∀ᵐ a ∂sampler.distribution, predicate a) ↔
      ∀ᵐ stream ∂fairCoinMeasure, predicate (sampler.run stream).1 :=
  ae_map_iff (measurable_fst.comp sampler.measurable).aemeasurable measurable

/-- The suffix returned by a completed fresh call is itself a fair stream. -/
theorem tail_map : fairCoinMeasure.map (fun stream => (sampler.run stream).2) = fairCoinMeasure := by
  have law := congrArg (Measure.map Prod.snd) sampler.fresh
  rw [Measure.map_map measurable_snd sampler.measurable,Measure.map_snd_prod] at law
  change fairCoinMeasure.map (fun stream => (sampler.run stream).2) =
    sampler.distribution Set.univ • fairCoinMeasure at law
  simpa only [measure_univ,one_smul] using law

theorem tail_ae {predicate : BitStream → Prop} (almost : ∀ᵐ stream ∂fairCoinMeasure, predicate stream) :
    ∀ᵐ stream ∂fairCoinMeasure, predicate (sampler.run stream).2 := by
  apply ae_of_ae_map (measurable_snd.comp sampler.measurable).aemeasurable
  change ∀ᵐ future ∂fairCoinMeasure.map (fun stream => (sampler.run stream).2), predicate future
  rw [tail_map]
  exact almost

end ComplexityOfGenerators.FreshStreamSampler
