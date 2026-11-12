import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.FixedRegionExecution
import ComplexityOfGenerators.Simulation.TransducerBank.RegionBounds
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O QC SC QB SB : Type} {k m : ℕ}
  (constructor : TapeBank Unit Bool Unit QC SC k) (source : TapeBank I A O QB SB m)

theorem source_regionRun (data : InputData I A) (choices : BitString) (length radius : ℕ)
    (ctor : BankConfiguration Unit QC SC k) (heads : ∀ tape,(ctor.head tape).natAbs≤radius)
    (result : Outcome O) (run : source.RegionRun data choices radius source.initialConfiguration result) :
    (sourceBank constructor source).RegionRun data choices radius (sourceConfiguration constructor source length ctor) result := by
  obtain ⟨ticks,finish,path,terminal⟩ := run
  have rightBound : ∀ tape,((frameHead ctor) tape).natAbs≤radius := by
    intro tape
    refine Fin.addCases (fun tape => ?_) (fun tape => ?_) tape
    · simpa [frameHead] using heads tape
    · simp [frameHead]
  exact ⟨ticks,LeftBankEmbedding.lift (encodeSource constructor.blank) (frameHead ctor)
      (frameTape constructor source length ctor) finish,
    LeftBankEmbedding.regionSteps_lift source (encodeSource constructor.blank) decodeSource (by intro;rfl)
      (frameHead ctor) (frameTape constructor source length ctor) rightBound path,
    LeftBankEmbedding.executes_lift source (encodeSource constructor.blank) decodeSource (by intro;rfl)
      (frameHead ctor) (frameTape constructor source length ctor) terminal⟩

theorem source_future_bound (data : InputData I A) (length radius : ℕ)
    (ctor : BankConfiguration Unit QC SC k) (heads : ∀ tape,(ctor.head tape).natAbs≤radius)
    (space : source.SpaceBound data radius)
    (termination : ∀ choices,∃ ticks result,source.Executes data choices source.initialConfiguration ticks result)
    (choices : BitString) (ticks : ℕ) (finish : BankConfiguration O QB (SourceSymbol SC SB) (m+(k+1)))
    (path : (sourceBank constructor source).Steps data choices (sourceConfiguration constructor source length ctor) ticks finish) :
    (sourceBank constructor source).Bounded data radius finish := by
  obtain ⟨time,result,run⟩ := termination choices
  have actual := source_regionRun constructor source data choices length radius ctor heads result
    (run.regionRun_of_prefixBound source (space choices))
  exact actual.bounds_prefix (sourceBank constructor source) path

theorem source_terminates (data : InputData I A) (length radius : ℕ)
    (ctor : BankConfiguration Unit QC SC k) (heads : ∀ tape,(ctor.head tape).natAbs≤radius)
    (space : source.SpaceBound data radius)
    (termination : ∀ choices,∃ ticks result,source.Executes data choices source.initialConfiguration ticks result)
    (choices : BitString) :
    ∃ ticks result,(sourceBank constructor source).Executes data choices (sourceConfiguration constructor source length ctor) ticks result := by
  obtain ⟨time,result,run⟩ := termination choices
  obtain ⟨ticks,actual⟩ := (source_regionRun constructor source data choices length radius ctor heads result
    (run.regionRun_of_prefixBound source (space choices))).executes (sourceBank constructor source)
  exact ⟨ticks,result,actual⟩

theorem source_accepted_iff (data : InputData I A) (choices : BitString) (length radius : ℕ)
    (ctor : BankConfiguration Unit QC SC k) (heads : ∀ tape,(ctor.head tape).natAbs≤radius)
    (space : source.SpaceBound data radius) (word : List O)
    (termination : ∃ ticks result,source.Executes data choices source.initialConfiguration ticks result) :
    (∃ ticks,(sourceBank constructor source).Executes data choices (sourceConfiguration constructor source length ctor) ticks (.accepted word)) ↔
      ∃ ticks,source.Executes data choices source.initialConfiguration ticks (.accepted word) := by
  constructor
  · rintro ⟨nativeTicks,accepted⟩
    obtain ⟨time,result,run⟩ := termination
    obtain ⟨ticks,actual⟩ := (source_regionRun constructor source data choices length radius ctor heads result
      (run.regionRun_of_prefixBound source (space choices))).executes (sourceBank constructor source)
    have same := accepted.unique (sourceBank constructor source) actual
    rw [← same.2] at run
    exact ⟨time,run⟩
  · rintro ⟨time,run⟩
    exact (source_regionRun constructor source data choices length radius ctor heads (.accepted word)
      (run.regionRun_of_prefixBound source (space choices))).executes (sourceBank constructor source)

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
