import ComplexityOfGenerators.Foundations.OriginalSourceSampler.Probability
import ComplexityOfGenerators.Foundations.OriginalSourceSampler.Semantics

/-! The genuine source sampler retains the original support and first
moments. In particular no bounded-output or second-moment hypothesis is used. -/
namespace ComplexityOfGenerators.Machine.OriginalSource
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

theorem seed_length_le_time {bits : BitString} (minimal : M.MinimalAcceptedSeed data bits) :
    bits.length≤time M data bits := by
  obtain ⟨finish,path,_,cursor⟩ := native_path M data minimal
  have bound := path.randomHead_le_time M
  simpa only [cursor,initialConfiguration,Nat.zero_add] using bound

theorem output_mem_language {bits : BitString} (minimal : M.MinimalAcceptedSeed data bits) :
    output M data bits∈M.generatedLanguage data :=
  (M.mem_generatedLanguage_iff_produces data _).mpr ⟨bits,produces_output M data minimal.1⟩

/-- Every original supported word is retained by a positive cylinder of
completed calls, however rare that word was in the source distribution. -/
theorem exists_seed_output {word : List O} (member : word∈M.generatedLanguage data) :
    ∃ bits, M.MinimalAcceptedSeed data bits ∧ output M data bits=word := by
  obtain ⟨bits,_,produced⟩ := member
  obtain ⟨short,initial,minimal⟩ := M.exists_minimal_accepted_prefix data bits ⟨word,produced⟩
  refine ⟨short,minimal,?_⟩
  exact M.produces_unique data bits _ word
    (M.produces_prefix initial (produces_output M data minimal.1)) produced

theorem streamProduces_iff (stream : BitStream) (word : List O) :
    M.streamProduces data stream word ↔
      ∃ bits,seed M data stream=some bits ∧ output M data bits=word := by
  constructor
  · intro produced
    have accepted : stream∈M.acceptedStreams data := by
      obtain ⟨bits,member,run⟩ := produced
      exact ⟨bits,member,word,run⟩
    obtain ⟨bits,selected,member,minimal⟩ := seed_spec M data accepted
    refine ⟨bits,selected,?_⟩
    exact M.streamProduces_unique data
      ⟨bits,member,produces_output M data minimal.1⟩ produced
  · rintro ⟨bits,selected,equal⟩
    have ⟨minimal,member⟩ := (seed_eq_some_iff M data stream bits).mp selected
    rw [← equal]
    exact ⟨bits,member,produces_output M data minimal.1⟩

theorem ae_native (generator : M.IsGenerator data) (active : (M.generatedLanguage data).Nonempty) :
    ∀ᵐ stream∂fairCoinMeasure, ∃ bits finish,
      seed M data stream=some bits ∧ stream∈cylinder bits ∧
      M.Steps data bits M.initialConfiguration (time M data bits) finish ∧
      M.observe data bits finish=.halted (.accepted (output M data bits)) ∧
      finish.randomHead=bits.length ∧
      M.streamRuntime data stream=(time M data bits : ℝ≥0∞) ∧
      M.streamLength data stream=(output M data bits).length := by
  filter_upwards [ae_accepted M data generator active] with stream accepted
  obtain ⟨bits,selected,member,minimal⟩ := seed_spec M data accepted
  obtain ⟨finish,path,terminal,cursor⟩ := native_path M data minimal
  exact ⟨bits,finish,selected,member,path,terminal,cursor,
    runtime_eq M data minimal.1 member,output_eq M data minimal.1 member⟩

theorem lintegral_recordedLength (generator : M.IsGenerator data)
    (active : (M.generatedLanguage data).Nonempty) :
    (∫⁻ stream,recordedLength M data (seed M data stream)∂fairCoinMeasure)=M.expectedLength data := by
  apply lintegral_congr_ae
  filter_upwards [ae_accepted M data generator active] with stream accepted
  exact recordedLength_eq M data accepted

theorem lintegral_recordedTime (generator : M.IsGenerator data)
    (active : (M.generatedLanguage data).Nonempty) :
    (∫⁻ stream,recordedTime M data (seed M data stream)∂fairCoinMeasure)=M.expectedRuntime data := by
  apply lintegral_congr_ae
  filter_upwards [ae_accepted M data generator active] with stream accepted
  exact recordedTime_eq M data accepted

/-- The actual independent-tail sampler has exactly the source's expected
output length. -/
theorem sampler_expectedLength (generator : M.IsGenerator data)
    (active : (M.generatedLanguage data).Nonempty) :
    (∫⁻ record,recordedLength M data record∂(sampler M data generator active).distribution)=
      M.expectedLength data := by
  change (∫⁻ record,recordedLength M data record∂fairCoinMeasure.map (seed M data))=_
  rw [lintegral_map (measurable_of_countable _) (measurable_seed M data)]
  exact lintegral_recordedLength M data generator active

/-- The recorded cost is the original primitive first runtime; no change to
the source distribution or higher-moment bound is hidden here. -/
theorem sampler_expectedRuntime (generator : M.IsGenerator data)
    (active : (M.generatedLanguage data).Nonempty) :
    (∫⁻ record,recordedTime M data record∂(sampler M data generator active).distribution)=
      M.expectedRuntime data := by
  change (∫⁻ record,recordedTime M data record∂fairCoinMeasure.map (seed M data))=_
  rw [lintegral_map (measurable_of_countable _) (measurable_seed M data)]
  exact lintegral_recordedTime M data generator active

end
end ComplexityOfGenerators.Machine.OriginalSource
