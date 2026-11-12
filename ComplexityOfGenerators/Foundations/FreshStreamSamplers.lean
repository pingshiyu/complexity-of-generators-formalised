import ComplexityOfGenerators.Foundations.RetryFreshBits

/-! Probability calculus for sequential use of one read-once fair stream.
This is not a computational or complexity interface: the native commands and
their cost proofs remain separate. The constructors below derive freshness
from concrete prefix splitting and first-success retrying. -/
namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
noncomputable section

structure FreshStreamSampler (A : Type) [MeasurableSpace A] where
  run : BitStream → A × BitStream
  measurable : Measurable run
  fresh : fairCoinMeasure.map run = (fairCoinMeasure.map (fun stream => (run stream).1)).prod fairCoinMeasure

namespace FreshStreamSampler
variable {A B : Type} [MeasurableSpace A] [MeasurableSpace B]

def distribution (sampler : FreshStreamSampler A) : Measure A :=
  fairCoinMeasure.map (fun stream => (sampler.run stream).1)

instance (sampler : FreshStreamSampler A) : IsProbabilityMeasure sampler.distribution := by
  exact (Measure.isProbabilityMeasure_map_iff (measurable_fst.comp sampler.measurable).aemeasurable).mpr inferInstance

def pure (value : A) : FreshStreamSampler A where
  run stream := (value, stream)
  measurable := measurable_const.prodMk measurable_id
  fresh := by
    apply Measure.ext_prod
    intro event future eventMeasurable futureMeasurable
    have runMeasurable : Measurable (fun stream : BitStream => (value, stream)) := measurable_const.prodMk measurable_id
    have valueMeasurable : Measurable (fun _stream : BitStream => value) := measurable_const
    rw [Measure.map_apply runMeasurable (eventMeasurable.prod futureMeasurable),
      Measure.prod_prod, Measure.map_apply valueMeasurable eventMeasurable]
    by_cases member : value ∈ event <;> simp [member]

noncomputable def readPrefix (width : ℕ) : FreshStreamSampler (Fin width → Bool) where
  run := splitStream width
  measurable := measurable_splitStream width
  fresh := by
    have marginal : fairCoinMeasure.map (fun stream => (splitStream width stream).1) = fairBlockMeasure width := by
      have law := congrArg (Measure.map Prod.fst) (fairCoinMeasure_map_splitStream width)
      rw [Measure.map_map measurable_fst (measurable_splitStream width), Measure.map_fst_prod,
        measure_univ, one_smul] at law
      exact law
    rw [fairCoinMeasure_map_splitStream, marginal]

noncomputable def retry (width : ℕ) (positive : 0 < width) (success : Set (Fin width → Bool))
    (measurable : MeasurableSet success) (mass : 0 < fairBlockMeasure width success) :
    FreshStreamSampler (ℕ × (Fin width → Bool)) where
  run stream := (retryRecord width success stream, retryTail width success stream)
  measurable := (measurable_retryRecord width success measurable).prodMk (measurable_retryTail width success measurable)
  fresh := fairCoinMeasure_map_retryRecord_tail width positive success measurable mass

/-- Apply an ordinary function to the completed value while retaining the
same unread stream. -/
noncomputable def map (sampler : FreshStreamSampler A) (f : A → B) (measurable : Measurable f) : FreshStreamSampler B where
  run stream := (f (sampler.run stream).1, (sampler.run stream).2)
  measurable := (measurable.comp (measurable_fst.comp sampler.measurable)).prodMk (measurable_snd.comp sampler.measurable)
  fresh := by
    apply Measure.ext_prod
    intro event future eventMeasurable futureMeasurable
    have runMeasurable : Measurable (fun stream => (f (sampler.run stream).1, (sampler.run stream).2)) :=
      (measurable.comp (measurable_fst.comp sampler.measurable)).prodMk (measurable_snd.comp sampler.measurable)
    have valueMeasurable : Measurable (fun stream => f (sampler.run stream).1) :=
      measurable.comp (measurable_fst.comp sampler.measurable)
    rw [Measure.map_apply runMeasurable (eventMeasurable.prod futureMeasurable),
      Measure.prod_prod, Measure.map_apply valueMeasurable eventMeasurable]
    have factored := congrArg (fun μ : Measure (A × BitStream) => μ ((f ⁻¹' event) ×ˢ future)) sampler.fresh
    rw [Measure.map_apply sampler.measurable ((measurable eventMeasurable).prod futureMeasurable),
      Measure.prod_prod] at factored
    have sourceMeasurable : Measurable (fun stream => (sampler.run stream).1) := measurable_fst.comp sampler.measurable
    rw [Measure.map_apply sourceMeasurable (measurable eventMeasurable)] at factored
    exact factored

section Bind
variable [Countable A] [MeasurableSingletonClass A]
    (sampler : FreshStreamSampler A) (next : A → FreshStreamSampler B)

private theorem measurable_next : Measurable (fun p : A × BitStream => (next p.1).run p.2) :=
  measurable_from_prod_countable_right (fun a => (next a).measurable)

/-- The exact conditional law for a subsequent call, even when the first
result chooses which sampler to run. -/
theorem bind_event (event : Set (B × BitStream)) (eventMeasurable : MeasurableSet event) :
    fairCoinMeasure {stream | (next (sampler.run stream).1).run (sampler.run stream).2 ∈ event} =
      ∫⁻ a, fairCoinMeasure ((next a).run ⁻¹' event) ∂sampler.distribution := by
  let follow := fun p : A × BitStream => (next p.1).run p.2
  have followMeasurable := measurable_next next
  have preimageMeasurable : MeasurableSet (follow ⁻¹' event) := followMeasurable eventMeasurable
  calc
    _ = (fairCoinMeasure.map sampler.run) (follow ⁻¹' event) :=
      (Measure.map_apply sampler.measurable preimageMeasurable).symm
    _ = (sampler.distribution.prod fairCoinMeasure) (follow ⁻¹' event) := by rw [sampler.fresh]; rfl
    _ = _ := Measure.prod_apply preimageMeasurable

noncomputable def bind : FreshStreamSampler B where
  run stream := (next (sampler.run stream).1).run (sampler.run stream).2
  measurable := (measurable_next next).comp sampler.measurable
  fresh := by
    apply Measure.ext_prod
    intro event future eventMeasurable futureMeasurable
    have actualMeasurable : Measurable (fun stream => (next (sampler.run stream).1).run (sampler.run stream).2) :=
      (measurable_next next).comp sampler.measurable
    have outputMeasurable : Measurable (fun stream => ((next (sampler.run stream).1).run (sampler.run stream).2).1) :=
      measurable_fst.comp actualMeasurable
    rw [Measure.map_apply actualMeasurable (eventMeasurable.prod futureMeasurable),
      Measure.prod_prod, Measure.map_apply outputMeasurable eventMeasurable]
    change fairCoinMeasure {stream | (next (sampler.run stream).1).run (sampler.run stream).2 ∈ event ×ˢ future} =
      fairCoinMeasure {stream | ((next (sampler.run stream).1).run (sampler.run stream).2).1 ∈ event} * fairCoinMeasure future
    rw [bind_event sampler next (event ×ˢ future) (eventMeasurable.prod futureMeasurable)]
    have each (a : A) : fairCoinMeasure ((next a).run ⁻¹' (event ×ˢ future)) =
        (next a).distribution event * fairCoinMeasure future := by
      have law := congrArg (fun μ : Measure (B × BitStream) => μ (event ×ˢ future)) (next a).fresh
      rw [Measure.map_apply (next a).measurable (eventMeasurable.prod futureMeasurable), Measure.prod_prod] at law
      exact law
    simp_rw [each]
    have marginal := bind_event sampler next (event ×ˢ Set.univ) (eventMeasurable.prod MeasurableSet.univ)
    have eachMarginal (a : A) : fairCoinMeasure ((next a).run ⁻¹' (event ×ˢ Set.univ)) = (next a).distribution event := by
      have valueMeasurable : Measurable (fun stream => ((next a).run stream).1) := measurable_fst.comp (next a).measurable
      rw [distribution, Measure.map_apply valueMeasurable eventMeasurable]
      congr 1
      ext stream
      simp
    simp_rw [eachMarginal] at marginal
    simp only [Set.mem_prod, Set.mem_univ, and_true] at marginal
    rw [marginal]
    exact lintegral_mul_const _ (measurable_of_countable _)

/-- Iterated integration for an adaptive fresh call. -/
theorem lintegral_bind (value : B → ℝ≥0∞) (valueMeasurable : Measurable value) :
    (∫⁻ stream, value ((sampler.bind next).run stream).1 ∂fairCoinMeasure) =
      ∫⁻ a, ∫⁻ future, value ((next a).run future).1 ∂fairCoinMeasure ∂sampler.distribution := by
  let h : A × BitStream → ℝ≥0∞ := fun p => value ((next p.1).run p.2).1
  have hm : Measurable h := valueMeasurable.comp (measurable_fst.comp (measurable_next next))
  change (∫⁻ stream, h (sampler.run stream) ∂fairCoinMeasure) = _
  rw [← lintegral_map hm sampler.measurable, sampler.fresh]
  exact lintegral_prod h hm.aemeasurable

end Bind
end FreshStreamSampler
end
end ComplexityOfGenerators
