import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Soundness
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Witnesses

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

/-- Every accepted input of length at most n has a real proposal prefix followed
by a real accepting source branch; every proposal coin leaves its source suffix
unread. Empty combined seeds are covered by accepted-prefix extension. -/
theorem generated_complete (language : Language α)
    (recognizes : ∀ word, (∃ bits, source.Accepts (decisionData word) bits) ↔ word ∈ language)
    (shortest : ∀ word ∈ language, fallback.length ≤ word.length)
    (n : ℕ) (word : Word α) (member : word ∈ language) (small : word.length ≤ n) :
    word ∈ (machine source fallback).generatedLanguage (generatorData n) := by
  obtain ⟨sourceBits, witness, sourceTicks, accepted⟩ := (recognizes word).mpr member
  obtain ⟨coins, proposalTicks, support⟩ := Proposal.complete source.program fallback n word small
  let bits := coins ++ sourceBits
  have prepared := long_index source.program fallback n ((shortest word member).trans small) bits
  have proposal := (support sourceBits).toSteps (bank source.program fallback)
  have onSuffix : source.Executes (decisionData word) (bits.drop coins.length) source.initialConfiguration
      sourceTicks (.accepted witness) := by
    simpa only [bits, List.drop_left] using accepted
  obtain ⟨ticks, _, execution⟩ := source_executes source.program fallback n bits word coins.length onSuffix
    (Nat.zero_le _)
  have before := prepared.trans (bank source.program fallback) proposal
  have full := before.executes (bank source.program fallback) execution
  apply ((machine source fallback).generatedLanguage_iff_produces (generatorData n) word).mpr
  refine ⟨bits, 2 * fallback.length + 2 + proposalTicks + ticks, ?_⟩
  exact full

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
