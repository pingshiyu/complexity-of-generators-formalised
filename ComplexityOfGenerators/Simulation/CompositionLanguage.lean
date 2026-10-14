import ComplexityOfGenerators.Simulation.CompositionCorrectness

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

/-- Join actual finite witnesses at the number of bits consumed by sampling,
not at the length of its original witness tape. Unused bits are discarded. -/
theorem composition_language_complete (n sampleTime : ℕ)
    (sample : S.TimeBound (generatorData n) sampleTime)
    (certificate : BitString) (sampled : certificate ∈ S.generatedLanguage (generatorData n))
    (word : List α) (recovered : word ∈ R.generatedLanguage (generatorData n certificate)) :
    word ∈ (samplerComposition S R).generatedLanguage (generatorData n) := by
  obtain ⟨samplingBits, _, produced⟩ := sampled
  obtain ⟨recoveryBits, positive, recoveryTime, recovery⟩ := recovered
  have source := S.produces_at_bound _ samplingBits sampleTime certificate (sample samplingBits) produced
  obtain ⟨terminal, ticks, _, path, halted, _, randomBound, _⟩ :=
    composition_sampler_prefix S R n samplingBits sampleTime (.accepted certificate) source
  obtain ⟨action, output⟩ := S.accepting_observation halted
  let bits := samplingBits.take terminal.randomHead ++ recoveryBits
  have path' := path.replace_suffix (samplerCompositionBank S R) randomBound recoveryBits
  have handoff := composition_handoff S R n bits terminal (by simpa [generatorData] using action)
  rw [output] at handoff
  have shift := R.runFrom_shift_random (generatorData n certificate)
    (samplingBits.take terminal.randomHead) recoveryBits R.initialConfiguration recoveryTime
  rw [Machine.runFrom_initial, recovery] at shift
  have shifted : R.runFrom (generatorData n certificate) bits
      {R.initialConfiguration with randomHead := terminal.randomHead} recoveryTime = .halted (.accepted word) := by
    simpa [bits, Machine.shiftRandomConfiguration, Machine.shiftRandomResult, Machine.initialConfiguration,
      List.length_take, Nat.min_eq_left randomBound] using shift
  obtain ⟨recoveryTicks, _, execution⟩ := composition_recoverer_executes S R n certificate bits
    terminal.work terminal.workHead {R.initialConfiguration with randomHead := terminal.randomHead}
    recoveryTime (.accepted word) shifted (Nat.zero_le _) (Nat.zero_le _)
  obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (samplerCompositionBank S R) _ bits _ _
    ((path'.trans _ handoff).executes _ execution)
  exact ⟨bits, by simp [bits, positive], nativeTicks, native⟩

theorem composition_language (n sampleTime recoveryTime : ℕ)
    (sample : S.TimeBound (generatorData n) sampleTime)
    (recover : ∀ certificate, certificate ∈ S.generatedLanguage (generatorData n) →
      R.TimeBound (generatorData n certificate) recoveryTime) :
    (samplerComposition S R).generatedLanguage (generatorData n) =
      {word | ∃ certificate, certificate ∈ S.generatedLanguage (generatorData n) ∧
        word ∈ R.generatedLanguage (generatorData n certificate)} := by
  ext word
  constructor
  · rintro ⟨bits, _, t, accepted⟩
    obtain ⟨ticks, result, _, execution, related⟩ := composition_executes S R n sampleTime recoveryTime bits sample recover
    obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (samplerCompositionBank S R) _ bits ticks result execution
    have same := (samplerComposition S R).halted_outcome_unique _ bits t nativeTicks _ _ accepted native
    subst result
    exact related
  · rintro ⟨certificate, sampled, recovered⟩
    exact composition_language_complete S R n sampleTime sample certificate sampled word recovered

end
end ComplexityOfGenerators.Simulation
