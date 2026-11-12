import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.Prepare
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness
import ComplexityOfGenerators.Simulation.TransducerBank.RegionBounds

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex

set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ} (source : TapeBank I A O Q S k)

theorem execution (data : InputData I A) (choices : BitString) (ticks : ℕ) (result : Outcome O)
    (run : source.Executes (sourceData data) choices source.initialConfiguration ticks result)
    (radius : ℕ) (space : source.SpaceBound (sourceData data) radius) :
    (bank source).RegionRun data choices (region data radius) (bank source).initialConfiguration result := by
  have actual := execution_inRegion source data choices source.initialConfiguration ticks result run radius (space choices)
  obtain ⟨time,preparing⟩ := prepare_steps source data choices
  exact actual.prepend (bank source) (preparing.mono (bank source) (Nat.le_max_right _ _))

theorem terminates (data : InputData I A) (radius : ℕ) (space : source.SpaceBound (sourceData data) radius)
    (termination : ∀ choices,∃ ticks result,source.Executes (sourceData data) choices source.initialConfiguration ticks result) :
    ∀ choices,∃ ticks result,(bank source).Executes data choices (bank source).initialConfiguration ticks result := by
  intro choices
  obtain ⟨ticks,result,run⟩ := termination choices
  obtain ⟨time,actual⟩ := (execution source data choices ticks result run radius space).executes (bank source)
  exact ⟨time,result,actual⟩

theorem spaceBound (data : InputData I A) (radius : ℕ) (space : source.SpaceBound (sourceData data) radius)
    (termination : ∀ choices,∃ ticks result,source.Executes (sourceData data) choices source.initialConfiguration ticks result) :
    (bank source).SpaceBound data (region data radius) := by
  apply TapeBank.spaceBound_of_regionRuns
  intro choices
  obtain ⟨ticks,result,run⟩ := termination choices
  exact ⟨result,execution source data choices ticks result run radius space⟩

/-- Exact fixed-choice acceptance, using the actual source termination
already required of generator members. -/
theorem accepted_iff (data : InputData I A) (choices : BitString) (word : List O)
    (radius : ℕ) (space : source.SpaceBound (sourceData data) radius)
    (termination : ∃ ticks result,source.Executes (sourceData data) choices source.initialConfiguration ticks result) :
    (∃ ticks,(bank source).Executes data choices (bank source).initialConfiguration ticks (.accepted word)) ↔
      ∃ ticks,source.Executes (sourceData data) choices source.initialConfiguration ticks (.accepted word) := by
  constructor
  · rintro ⟨nativeTicks,accepted⟩
    obtain ⟨ticks,result,run⟩ := termination
    obtain ⟨time,actual⟩ := (execution source data choices ticks result run radius space).executes (bank source)
    have same := accepted.unique (bank source) actual
    rw [← same.2] at run
    exact ⟨ticks,run⟩
  · rintro ⟨ticks,run⟩
    exact (execution source data choices ticks (.accepted word) run radius space).executes (bank source)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
