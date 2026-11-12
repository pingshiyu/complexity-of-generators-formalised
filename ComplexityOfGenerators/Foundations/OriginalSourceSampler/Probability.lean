import ComplexityOfGenerators.Foundations.OriginalSourceSampler.Seeds

/-! A completed original source call leaves an independent fair stream after
exactly its consumed bits. This uses the actual minimal accepting prefix
partition, rather than an assumed independent source-call interface. -/
namespace ComplexityOfGenerators.Machine.OriginalSource
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

private def codeEvent (event : Set (Option BitString)) (bits : BitString) : Set BitStream :=
  {stream | seed M data stream=some bits ∧ some bits∈event}

private theorem codeEvent_description (event : Set (Option BitString)) (bits : BitString) :
    codeEvent M data event bits=
      {_stream : BitStream | M.MinimalAcceptedSeed data bits ∧ some bits∈event} ∩ cylinder bits := by
  ext stream
  simp only [codeEvent,Set.mem_ofPred_eq,seed_eq_some_iff,Set.mem_inter_iff]
  tauto

private theorem codeEvent_measurable (event : Set (Option BitString)) (bits : BitString) :
    MeasurableSet (codeEvent M data event bits) := by
  classical
  rw [codeEvent_description]
  by_cases valid : M.MinimalAcceptedSeed data bits ∧ some bits∈event
  · simpa [valid] using measurableSet_cylinder bits
  · simp [valid]

private theorem codeEvents_disjoint (event : Set (Option BitString)) :
    Pairwise (fun first second => Disjoint
      (codeEvent M data event first) (codeEvent M data event second)) := by
  intro first second different
  apply Set.disjoint_left.mpr
  rintro stream ⟨left,_⟩ ⟨right,_⟩
  exact different (Option.some.inj (left.symm.trans right))

private theorem codeEvent_determined (event : Set (Option BitString)) (bits : BitString)
    (left right : BitStream) (same : (splitStream bits.length left).1=(splitStream bits.length right).1) :
    left∈codeEvent M data event bits ↔ right∈codeEvent M data event bits := by
  rw [codeEvent_description]
  have equal : ∀ i : Fin bits.length,left i=right i := fun i => congrFun same i
  change ((M.MinimalAcceptedSeed data bits ∧ some bits∈event) ∧ (∀ i : Fin bits.length,left i=bits[i])) ↔
    ((M.MinimalAcceptedSeed data bits ∧ some bits∈event) ∧ ∀ i : Fin bits.length,right i=bits[i])
  simp_rw [equal]

private theorem event_partition (event : Set (Option BitString))
    (accepted : ∀ᵐ stream∂fairCoinMeasure,stream∈M.acceptedStreams data) :
    {stream | seed M data stream∈event}=ᵐ[fairCoinMeasure]
      ⋃ bits,codeEvent M data event bits := by
  filter_upwards [accepted] with stream accepted
  obtain ⟨bits,selected,_⟩ := seed_spec M data accepted
  apply propext
  constructor
  · intro member
    exact Set.mem_iUnion.mpr ⟨bits,selected,selected ▸ member⟩
  · intro member
    obtain ⟨other,equal,target⟩ := Set.mem_iUnion.mp member
    exact equal.symm ▸ target

private theorem future_partition (event : Set (Option BitString)) (future : Set BitStream)
    (accepted : ∀ᵐ stream∂fairCoinMeasure,stream∈M.acceptedStreams data) :
    {stream | seed M data stream∈event ∧ tail M data stream∈future}=ᵐ[fairCoinMeasure]
      ⋃ bits,codeEvent M data event bits ∩ {stream | (splitStream bits.length stream).2∈future} := by
  filter_upwards [accepted] with stream accepted
  obtain ⟨bits,selected,_⟩ := seed_spec M data accepted
  apply propext
  constructor
  · rintro ⟨member,remaining⟩
    refine Set.mem_iUnion.mpr ⟨bits,⟨selected,selected ▸ member⟩,?_⟩
    change (splitStream bits.length stream).2∈future
    rwa [← tail_of_seed M data selected]
  · intro member
    obtain ⟨other,⟨equal,target⟩,remaining⟩ := Set.mem_iUnion.mp member
    exact ⟨equal.symm ▸ target,by rwa [tail_of_seed M data equal]⟩

/-- Exact independence of the entire consumed prefix and the unread suffix,
for an arbitrary active native generator. -/
theorem seed_future (generator : M.IsGenerator data)
    (active : (M.generatedLanguage data).Nonempty)
    (event : Set (Option BitString)) (future : Set BitStream) (futureMeasurable : MeasurableSet future) :
    fairCoinMeasure {stream | seed M data stream∈event ∧ tail M data stream∈future}=
      fairCoinMeasure {stream | seed M data stream∈event}*fairCoinMeasure future := by
  have accepted := ae_accepted M data generator active
  have measurable := codeEvent_measurable M data event
  have disjoint := codeEvents_disjoint M data event
  have jointDisjoint : Pairwise (fun first second => Disjoint
      (codeEvent M data event first ∩ {stream | (splitStream first.length stream).2∈future})
      (codeEvent M data event second ∩ {stream | (splitStream second.length stream).2∈future})) := by
    intro first second different
    exact (disjoint different).mono Set.inter_subset_left Set.inter_subset_left
  rw [measure_congr (future_partition M data event future accepted),
    measure_congr (event_partition M data event accepted),
    measure_iUnion jointDisjoint (fun bits => (measurable bits).inter
      ((measurable_snd.comp (measurable_splitStream bits.length)) futureMeasurable)),
    measure_iUnion disjoint measurable]
  simp_rw [fairCoinMeasure_prefix_event_tail _ _ _ (codeEvent_determined M data event _) futureMeasurable]
  exact ENNReal.tsum_mul_right

theorem map_seed_tail (generator : M.IsGenerator data)
    (active : (M.generatedLanguage data).Nonempty) :
    fairCoinMeasure.map (fun stream => (seed M data stream,tail M data stream))=
      (fairCoinMeasure.map (seed M data)).prod fairCoinMeasure := by
  apply Measure.ext_prod
  intro event future eventMeasurable futureMeasurable
  rw [Measure.map_apply ((measurable_seed M data).prodMk (measurable_tail M data))
    (eventMeasurable.prod futureMeasurable),Measure.prod_prod,
    Measure.map_apply (measurable_seed M data) eventMeasurable]
  exact seed_future M data generator active event future futureMeasurable

/-- A genuine original-source sampler. The native execution and its exact
consumed-prefix interpretation are proved separately in `Paths`/`Semantics`. -/
def sampler (generator : M.IsGenerator data) (active : (M.generatedLanguage data).Nonempty) :
    FreshStreamSampler (Option BitString) where
  run stream := (seed M data stream,tail M data stream)
  measurable := (measurable_seed M data).prodMk (measurable_tail M data)
  fresh := map_seed_tail M data generator active

end
end ComplexityOfGenerators.Machine.OriginalSource
