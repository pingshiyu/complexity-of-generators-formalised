import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceSpace
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.ShortIndexSpace

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

def totalRadius (n sourceRadius : ℕ) : ℕ := sourceRadius + 3 * n + fallback.length + 3

/-- All actual proposal, source, and output prefixes stay in one fixed work
region. Short-index draining is included without charging the random-tape length
as space. The source's running time never appears in this bound. -/
theorem machine_spaceBound (termination : ∀ word, source.Terminates (decisionData word))
    (n radius : ℕ) (bounded : ∀ word, word.length ≤ n → source.SpaceBound (decisionData word) radius) :
    (machine source fallback).SpaceBound (generatorData n) (totalRadius fallback n radius) := by
  change (bank source.program fallback).SpaceBound (generatorData n) (totalRadius fallback n radius)
  apply TapeBank.spaceBound_of_regionRuns
  intro bits
  by_cases short : n < fallback.length
  · exact ⟨.exhausted, (short_index_region source.program fallback n short bits).mono
      (bank source.program fallback) (Nat.zero_le _)⟩
  · have prepared := (long_index_region source.program fallback n (by omega) bits).mono
      (bank source.program fallback) (Nat.zero_le (totalRadius fallback n radius))
    obtain ⟨proposalTicks, _, result⟩ := Proposal.runs source.program fallback n bits
    rcases result with exhausted | ⟨word, consumed, wordSmall, consumedSmall, path⟩
    · obtain ⟨finish, path, terminal⟩ := exhausted
      have run : (bank source.program fallback).RegionRun (generatorData n) bits n
          {(bank source.program fallback).initialConfiguration with state := .guess} .exhausted :=
        ⟨proposalTicks, finish, path, terminal⟩
      have widened := run.mono (bank source.program fallback) (show n ≤ totalRadius fallback n radius by
        unfold totalRadius; omega)
      exact ⟨.exhausted, widened.prepend (bank source.program fallback) prepared⟩
    · obtain ⟨ticks, result, execution⟩ := termination word (bits.drop consumed)
      have sourceRun := source_regionRun source.program fallback n bits word consumed execution radius
        (bounded word wordSmall (bits.drop consumed))
      have fits : sourceRadius fallback word radius ≤ totalRadius fallback n radius := by
        unfold sourceRadius totalRadius
        omega
      have before := prepared.trans (bank source.program fallback)
        (path.mono (bank source.program fallback) (by unfold totalRadius; omega))
      exact ⟨sourceOutcome word fallback result,
        (sourceRun.mono (bank source.program fallback) fits).prepend (bank source.program fallback) before⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
