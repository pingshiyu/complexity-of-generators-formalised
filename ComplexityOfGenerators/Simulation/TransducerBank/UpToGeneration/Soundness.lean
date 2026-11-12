import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Generability

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

theorem generated_sound (language : Language α)
    (termination : ∀ word, source.Terminates (decisionData word))
    (recognizes : ∀ word, (∃ bits, source.Accepts (decisionData word) bits) ↔ word ∈ language)
    (fallbackMember : fallback ∈ language) (n : ℕ) (output : Word α)
    (generated : output ∈ (machine source fallback).generatedLanguage (generatorData n)) :
    output ∈ language ∧ output.length ≤ n := by
  obtain ⟨bits, _, ticks, accepted⟩ := generated
  by_cases short : n < fallback.length
  · exact False.elim ((short_no_accepts source fallback n short bits) ⟨output, ticks, accepted⟩)
  · have prepared := long_index source.program fallback n (by omega) bits
    obtain ⟨proposalTicks, _, result⟩ := Proposal.runs source.program fallback n bits
    rcases result with exhausted | ⟨word, consumed, wordSmall, consumedSmall, path⟩
    · have actual := prepared.executes (bank source.program fallback) (exhausted.executes source.program fallback)
      have impossible := (TapeBank.Executes.unique (bank source.program fallback) accepted actual).2
      cases impossible
    · obtain ⟨sourceTicks, result, execution⟩ := termination word (bits.drop consumed)
      obtain ⟨targetTicks, _, simulated⟩ := source_executes source.program fallback n bits word consumed execution
        (Nat.zero_le _)
      have before := prepared.trans (bank source.program fallback) (path.toSteps _)
      have actual := before.executes (bank source.program fallback) simulated
      have same := (TapeBank.Executes.unique (bank source.program fallback) accepted actual).2
      exact source_result_sound source fallback language recognizes fallbackMember n word output
        wordSmall (by omega) (bits.drop consumed) sourceTicks result execution same.symm

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
