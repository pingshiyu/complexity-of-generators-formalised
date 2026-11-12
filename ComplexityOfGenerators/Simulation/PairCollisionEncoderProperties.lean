import ComplexityOfGenerators.Simulation.PairCollisionEncoder

namespace ComplexityOfGenerators.Simulation.PairCollisionEncoder
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal
variable {I A : Type} (M : Machine I A PairSymbol)

theorem produces (data : InputData I A) (bits : BitString) (word : List PairSymbol)
    (source : M.Produces data bits word) :
    (machine M).Produces data bits (binaryPairWord word) := by
  obtain ⟨t,source⟩ := source
  exact ⟨2*t,by rw [run,source];rfl⟩

theorem produces_iff (data : InputData I A) (bits word : BitString) :
    (machine M).Produces data bits word ↔
      ∃ source : List PairSymbol,word=binaryPairWord source ∧ M.Produces data bits source := by
  constructor
  · rintro ⟨t,accepted⟩
    have padded := (machine M).run_halted_add data bits t (.accepted word) accepted t
    rw [show t+t=2*t by omega,run] at padded
    cases source : M.run data bits t with
    | running c => simp [source,result] at padded
    | halted terminal =>
        cases terminal with
        | accepted output =>
            have same : binaryPairWord output=word := by simpa [source,result,outcome] using padded
            exact ⟨output,same.symm,t,source⟩
        | rejected => simp [source,result,outcome] at padded
        | exhausted => simp [source,result,outcome] at padded
  · rintro ⟨source,rfl,accepted⟩
    exact produces M data bits source accepted

theorem halting (data : InputData I A) (source : M.HaltingTransducer data) :
    (machine M).HaltingTransducer data := by
  constructor
  · intro bits
    obtain ⟨t,terminal,accepted⟩ := source.1 bits
    exact ⟨2*t,outcome terminal,by rw [run,accepted];rfl⟩
  · intro bits t rejected
    have padded := (machine M).run_halted_add data bits t .rejected rejected t
    rw [show t+t=2*t by omega,run] at padded
    cases sourceRun : M.run data bits t with
    | running c => simp [sourceRun,result] at padded
    | halted terminal =>
        cases terminal with
        | rejected => exact source.2 bits t sourceRun
        | accepted word => simp [sourceRun,result,outcome] at padded
        | exhausted => simp [sourceRun,result,outcome] at padded

theorem acceptedStreams (data : InputData I A) :
    (machine M).acceptedStreams data=M.acceptedStreams data := by
  ext stream
  constructor
  · rintro ⟨bits,cylinder,word,produced⟩
    obtain ⟨source,encoded,sourceRun⟩ := (produces_iff M data bits word).mp produced
    exact ⟨bits,cylinder,source,sourceRun⟩
  · rintro ⟨bits,cylinder,word,produced⟩
    exact ⟨bits,cylinder,binaryPairWord word,produces M data bits word produced⟩

theorem isGenerator (data : InputData I A) (source : M.IsGenerator data) :
    (machine M).IsGenerator data := by
  refine ⟨halting M data source.1,?_⟩
  simpa only [acceptedStreams] using source.2

theorem generatedLanguage (data : InputData I A) :
    (machine M).generatedLanguage data=binaryPairWord '' M.generatedLanguage data := by
  ext word
  constructor
  · rintro ⟨bits,nonempty,accepted⟩
    obtain ⟨source,encoded,sourceRun⟩ := (produces_iff M data bits word).mp accepted
    exact ⟨source,⟨bits,nonempty,sourceRun⟩,encoded.symm⟩
  · rintro ⟨source,⟨bits,nonempty,sourceRun⟩,rfl⟩
    exact ⟨bits,nonempty,produces M data bits source sourceRun⟩

theorem streamProduces (data : InputData I A) (stream : BitStream) (word : List PairSymbol)
    (source : M.streamProduces data stream word) :
    (machine M).streamProduces data stream (binaryPairWord word) := by
  obtain ⟨bits,cylinder,source⟩ := source
  exact ⟨bits,cylinder,produces M data bits word source⟩

theorem streamLength (data : InputData I A) (stream : BitStream) :
    (machine M).streamLength data stream=2*M.streamLength data stream := by
  by_cases accepted : stream∈M.acceptedStreams data
  · obtain ⟨bits,cylinder,word,source⟩ := accepted
    have produced : M.streamProduces data stream word := ⟨bits,cylinder,source⟩
    rw [(machine M).streamLength_of_produces data (streamProduces M data stream word produced),
      M.streamLength_of_produces data produced,binaryPairWord_length]
  · have encodedAbsent : stream∉(machine M).acceptedStreams data := by simpa only [acceptedStreams] using accepted
    rw [M.streamLength_eq_zero_of_not_accepted data accepted,
      (machine M).streamLength_eq_zero_of_not_accepted data encodedAbsent]

theorem expectedLength (data : InputData I A) :
    (machine M).expectedLength data=2*M.expectedLength data := by
  unfold Machine.expectedLength
  simp only [streamLength,Nat.cast_mul,Nat.cast_ofNat]
  simpa only [Function.comp_apply] using lintegral_const_mul (2 : ℝ≥0∞)
    ((measurable_of_countable (fun n : ℕ => (n : ℝ≥0∞))).comp (M.measurable_streamLength data))

theorem streamRuntime_le (data : InputData I A) (stream : BitStream) :
    (machine M).streamRuntime data stream≤2*M.streamRuntime data stream := by
  classical
  by_cases accepted : stream∈M.acceptedStreams data
  · have existsTime : ∃ t,M.streamAcceptsBy data stream t := by
      obtain ⟨bits,cylinder,word,t,source⟩ := accepted
      exact ⟨t,bits,word,cylinder,source⟩
    let t := Nat.find existsTime
    have atTime := Nat.find_spec existsTime
    have runtime : M.streamRuntime data stream=(t : ℝ≥0∞) :=
      M.streamRuntime_eq_of_first_acceptsBy data atTime (fun s earlier=>Nat.find_min existsTime earlier)
    obtain ⟨bits,word,cylinder,source⟩ := atTime
    have target : (machine M).streamAcceptsBy data stream (2*t) :=
      ⟨bits,binaryPairWord word,cylinder,by rw [run,source];rfl⟩
    exact ((machine M).streamRuntime_le_of_acceptsBy data target).trans_eq (by simp [runtime])
  · rw [M.streamRuntime_eq_top_of_not_accepted data accepted]
    simp

theorem expectedRuntime_le (data : InputData I A) :
    (machine M).expectedRuntime data≤2*M.expectedRuntime data := by
  unfold Machine.expectedRuntime
  apply le_trans (lintegral_mono (streamRuntime_le M data))
  rw [lintegral_const_mul _ (M.measurable_streamRuntime data)]

end
end ComplexityOfGenerators.Simulation.PairCollisionEncoder
