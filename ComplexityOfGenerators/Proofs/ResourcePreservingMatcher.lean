import ComplexityOfGenerators.Proofs.ResourceGeneration
import ComplexityOfGenerators.Simulation.OutputMatcherSpace

/-! The simulation core for arbitrary-resource containments. The matcher uses
exactly the source work tape and one transition per source transition. Its
read-only family index must already have been supplied; the ordinary-input
index preparation and a resource-constructible clock remain separate steps. -/

namespace ComplexityOfGenerators.Simulation
noncomputable section
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

theorem outputMatcher_timeBound (data : InputData α Bool) (time : ℕ)
    (bound : M.TimeBound (matcherSourceData data) time) :
    (outputMatcher M).TimeBound data time := by
  intro bits
  obtain ⟨result, halted⟩ := bound bits
  exact ⟨matcherOutcome data.input result, by rw [outputMatcher_run, halted]; rfl⟩

/-- Accepting-time bounds are preserved even if unsuccessful runs are unbounded. -/
theorem outputMatcher_acceptingTimeBound (data : InputData α Bool) (time : ℕ)
    (bound : M.AcceptingTimeBound (matcherSourceData data) time) :
    (outputMatcher M).AcceptingTimeBound data time := by
  intro bits out produced
  have source := (outputMatcher_accepts_iff M data bits).mp ⟨out, produced⟩
  have target : (outputMatcher M).run data bits time = .halted (.accepted []) := by
    rw [outputMatcher_run, bound bits data.input source]
    simp [matcherResult, matcherOutcome]
  obtain ⟨ticks, accepted⟩ := produced
  have equal := (outputMatcher M).halted_outcome_unique data bits ticks time
    (.accepted out) (.accepted []) accepted target
  have output : out = [] := Outcome.accepted.inj equal
  simpa only [output] using target

theorem outputMatcher_layer (G : UniformGenerators α) (word : List α) :
    (∃ bits, (outputMatcher G.machine).Accepts ⟨word, [], word.length⟩ bits) ↔
      word ∈ G.layer word.length := by
  simp only [outputMatcher_accepts_iff]
  exact (G.machine.mem_generatedLanguage_iff_produces (generatorData word.length) word).symm

/-- The core simulation preserves both arbitrary resource bounds exactly.
The tuple input includes the read-only unary family index; this theorem does
not silently identify that representation with ordinary-input resource classes. -/
theorem exact_family_resource_matcher (G : GeneratorFamily α) (time space : ℕ → ℕ)
    (accepting : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (time n))
    (bounded : G.toUniformGenerators.RunsInSpace space) :
    ∃ R : Machine α Bool Unit, ∀ word,
      ((∃ bits, R.Accepts ⟨word, [], word.length⟩ bits) ↔ word ∈ G.toUniformGenerators.language) ∧
      R.AcceptingTimeBound ⟨word, [], word.length⟩ (time word.length) ∧
      R.SpaceBound ⟨word, [], word.length⟩ (space word.length) := by
  refine ⟨outputMatcher G.machine, fun word => ⟨?_, ?_, ?_⟩⟩
  · rw [outputMatcher_layer]
    rw [G.layer_eq_lengthSlice]
    simp only [lengthSlice, Set.mem_ofPred_eq, and_true]
  · exact outputMatcher_acceptingTimeBound G.machine _ _ (accepting word.length)
  · exact outputMatcher_spaceBound G.machine _ _ (bounded word.length)

end
end ComplexityOfGenerators.Simulation
