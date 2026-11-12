import ComplexityOfGenerators.Foundations.FreshBits

/-! First-success retrying leaves an independent fair unread stream. The
record retains both the selected block and the number of attempts, allowing
later controllers to account for output means and elapsed-time moments. -/
namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false

noncomputable def retryRecord (width : ℕ) (success : Set (Fin width → Bool)) (stream : BitStream) :
    ℕ × (Fin width → Bool) :=
  (firstSuccessIndex width success stream, selectedBlock width success stream)

noncomputable def retryTail (width : ℕ) (success : Set (Fin width → Bool)) (stream : BitStream) : BitStream :=
  (splitStream ((firstSuccessIndex width success stream + 1) * width) stream).2

theorem measurable_retryRecord (width : ℕ) (success : Set (Fin width → Bool))
    (measurable : MeasurableSet success) : Measurable (retryRecord width success) :=
  (measurable_firstSuccessIndex width success measurable).prodMk (measurable_selectedBlock width success measurable)

theorem measurable_retryTail (width : ℕ) (success : Set (Fin width → Bool))
    (measurable : MeasurableSet success) : Measurable (retryTail width success) := by
  let shift : ℕ × BitStream → BitStream := fun p => (splitStream ((p.1+1)*width) p.2).2
  have shifted : Measurable shift := by
    apply measurable_from_prod_countable_right
    intro n
    exact measurable_snd.comp (measurable_splitStream ((n+1)*width))
  exact shifted.comp ((measurable_firstSuccessIndex width success measurable).prodMk measurable_id)

private def recordTarget (width : ℕ) (success : Set (Fin width → Bool))
    (event : Set (ℕ × (Fin width → Bool))) (n : ℕ) : Set (Fin width → Bool) :=
  {bits | (n, bits) ∈ event ∧ bits ∈ success}

private theorem recordHits_disjoint (width : ℕ) (success : Set (Fin width → Bool))
    (event : Set (ℕ × (Fin width → Bool))) :
    Pairwise (fun n m => Disjoint
      (retryHit width success (recordTarget width success event n) n)
      (retryHit width success (recordTarget width success event m) m)) := by
  intro n m different
  apply (retryHits_pairwiseDisjoint width success success (Set.Subset.refl _) different).mono
  · exact fun _ hit => ⟨hit.1, hit.2.2⟩
  · exact fun _ hit => ⟨hit.1, hit.2.2⟩

private theorem record_event_partition (width : ℕ) (positive : 0 < width)
    (success : Set (Fin width → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure width success) (event : Set (ℕ × (Fin width → Bool))) :
    {stream | retryRecord width success stream ∈ event} =ᵐ[fairCoinMeasure]
      ⋃ n, retryHit width success (recordTarget width success event n) n := by
  filter_upwards [firstSuccessIndex_ae_success width positive success measurable mass] with stream hit
  apply propext
  constructor
  · intro member
    apply Set.mem_iUnion.mpr
    refine ⟨firstSuccessIndex width success stream, ?_, member, hit⟩
    rcases firstSuccessIndex_spec width success stream with ⟨_, minimal⟩ | ⟨_, never⟩
    · exact minimal
    · exact fun j _ => never j
  · intro member
    obtain ⟨n, found⟩ := Set.mem_iUnion.mp member
    have equal := firstSuccessIndex_eq_of_retryHit width success (recordTarget width success event n)
      (fun _ target => target.2) stream n found
    change (firstSuccessIndex width success stream, selectedBlock width success stream) ∈ event
    simpa only [selectedBlock, equal] using found.2.1

private theorem record_future_partition (width : ℕ) (positive : 0 < width)
    (success : Set (Fin width → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure width success) (event : Set (ℕ × (Fin width → Bool))) (future : Set BitStream) :
    {stream | retryRecord width success stream ∈ event ∧ retryTail width success stream ∈ future} =ᵐ[fairCoinMeasure]
      ⋃ n, retryHit width success (recordTarget width success event n) n ∩
        {stream | (splitStream ((n+1)*width) stream).2 ∈ future} := by
  filter_upwards [record_event_partition width positive success measurable mass event] with stream equal
  apply propext
  constructor
  · rintro ⟨record, tail⟩
    obtain ⟨n, found⟩ := Set.mem_iUnion.mp (equal.mp record)
    have index := firstSuccessIndex_eq_of_retryHit width success (recordTarget width success event n)
      (fun _ target => target.2) stream n found
    refine Set.mem_iUnion.mpr ⟨n, found, ?_⟩
    dsimp only [retryTail] at tail
    rw [index] at tail
    exact tail
  · intro member
    obtain ⟨n, found, tail⟩ := Set.mem_iUnion.mp member
    have index := firstSuccessIndex_eq_of_retryHit width success (recordTarget width success event n)
      (fun _ target => target.2) stream n found
    refine ⟨equal.mpr (Set.mem_iUnion.mpr ⟨n, found⟩), ?_⟩
    change (splitStream ((n+1)*width) stream).2 ∈ future at tail
    change (splitStream ((firstSuccessIndex width success stream+1)*width) stream).2 ∈ future
    rw [index]
    exact tail

/-- Even the completed retry count and selected value together are independent
of all unread bits. -/
theorem fairCoinMeasure_retryRecord_future (width : ℕ) (positive : 0 < width)
    (success : Set (Fin width → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure width success) (event : Set (ℕ × (Fin width → Bool)))
    (future : Set BitStream) (futureMeasurable : MeasurableSet future) :
    fairCoinMeasure {stream | retryRecord width success stream ∈ event ∧ retryTail width success stream ∈ future} =
      fairCoinMeasure {stream | retryRecord width success stream ∈ event} * fairCoinMeasure future := by
  have hitsMeasurable (n : ℕ) : MeasurableSet (retryHit width success (recordTarget width success event n) n) :=
    measurableSet_retryHit width success _ measurable (Set.to_countable _ |>.measurableSet) n
  have disjoint := recordHits_disjoint width success event
  have jointDisjoint : Pairwise (fun n m => Disjoint
      (retryHit width success (recordTarget width success event n) n ∩
        {stream | (splitStream ((n+1)*width) stream).2 ∈ future})
      (retryHit width success (recordTarget width success event m) m ∩
        {stream | (splitStream ((m+1)*width) stream).2 ∈ future})) := by
    intro n m different
    exact (disjoint different).mono Set.inter_subset_left Set.inter_subset_left
  rw [measure_congr (record_future_partition width positive success measurable mass event future),
    measure_congr (record_event_partition width positive success measurable mass event),
    measure_iUnion jointDisjoint (fun n => (hitsMeasurable n).inter
      ((measurable_snd.comp (measurable_splitStream ((n+1)*width))) futureMeasurable)),
    measure_iUnion disjoint hitsMeasurable]
  simp_rw [fairCoinMeasure_retryHit_tail width _ success _ future futureMeasurable]
  exact ENNReal.tsum_mul_right

/-- The actual unread suffix following a successful retry is fair. -/
theorem fairCoinMeasure_map_retryTail (width : ℕ) (positive : 0 < width)
    (success : Set (Fin width → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure width success) :
    fairCoinMeasure.map (retryTail width success) = fairCoinMeasure := by
  apply Measure.ext
  intro future futureMeasurable
  rw [Measure.map_apply (measurable_retryTail width success measurable) futureMeasurable]
  change fairCoinMeasure {stream | retryTail width success stream ∈ future} = fairCoinMeasure future
  simpa only [Set.mem_univ, true_and, Set.ofPred_true, measure_univ, one_mul] using
    fairCoinMeasure_retryRecord_future width positive success measurable mass Set.univ future futureMeasurable

/-- The joint stopping record and fresh suffix have a product distribution,
proved from the concrete fair-coin stream rather than postulated by a sampler. -/
theorem fairCoinMeasure_map_retryRecord_tail (width : ℕ) (positive : 0 < width)
    (success : Set (Fin width → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure width success) :
    fairCoinMeasure.map (fun stream => (retryRecord width success stream, retryTail width success stream)) =
      (fairCoinMeasure.map (retryRecord width success)).prod fairCoinMeasure := by
  apply Measure.ext_prod
  intro event future eventMeasurable futureMeasurable
  rw [Measure.map_apply ((measurable_retryRecord width success measurable).prodMk
      (measurable_retryTail width success measurable)) (eventMeasurable.prod futureMeasurable),
    Measure.prod_prod, Measure.map_apply (measurable_retryRecord width success measurable) eventMeasurable]
  exact fairCoinMeasure_retryRecord_future width positive success measurable mass event future futureMeasurable

end ComplexityOfGenerators

namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal

/-- An arbitrary subsequent computation can be integrated over a genuinely
fresh stream, even when it depends on the completed retry record. -/
theorem lintegral_retryRecord_tail (width : ℕ) (positive : 0 < width)
    (success : Set (Fin width → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure width success)
    (value : (ℕ × (Fin width → Bool)) × BitStream → ℝ≥0∞) (valueMeasurable : Measurable value) :
    (∫⁻ stream, value (retryRecord width success stream, retryTail width success stream) ∂fairCoinMeasure) =
      ∫⁻ record, ∫⁻ future, value (record, future) ∂fairCoinMeasure
        ∂(fairCoinMeasure.map (retryRecord width success)) := by
  rw [← lintegral_map valueMeasurable ((measurable_retryRecord width success measurable).prodMk
      (measurable_retryTail width success measurable)),
    fairCoinMeasure_map_retryRecord_tail width positive success measurable mass,
    lintegral_prod value valueMeasurable.aemeasurable]

end ComplexityOfGenerators
