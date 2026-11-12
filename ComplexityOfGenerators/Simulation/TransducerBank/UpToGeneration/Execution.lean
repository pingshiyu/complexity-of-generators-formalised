import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceSemantics
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.ShortIndex
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Runs
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

def trialBudget (n sourceTime : ℕ) : ℕ :=
  (Fintype.card α + 10) * (n + 1) + 3 * sourceTime + 2 * n + 3 * fallback.length + 5

/-- Short indices drain real bits, so their finite executions need not have a
common time deadline. They never produce a word. -/
theorem short_no_accepts (n : ℕ) (short : n < fallback.length) (bits : BitString) :
    ¬ (machine source fallback).Accepts (generatorData n) bits := by
  rintro ⟨word, ticks, accepted⟩
  obtain ⟨otherTicks, _, exhausted⟩ := short_index source.program fallback n short bits
  have same := (TapeBank.Executes.unique (bank source.program fallback) accepted exhausted).2
  cases same

/-- A productive index runs the finite proposal and then the actual source
branch. The deadline is an analysis bound, not a value queried by the program. -/
theorem long_timeBound (n : ℕ) (long : fallback.length ≤ n) (sourceTime : ℕ)
    (bounded : ∀ word, word.length ≤ n → source.TimeBound (decisionData word) sourceTime) :
    (machine source fallback).TimeBound (generatorData n) (trialBudget fallback n sourceTime) := by
  intro bits
  change ∃ ticks result, ticks ≤ trialBudget fallback n sourceTime ∧
    (bank source.program fallback).Executes (generatorData n) bits
      (bank source.program fallback).initialConfiguration ticks result
  have prepared := long_index source.program fallback n long bits
  obtain ⟨proposalTicks, proposalCost, result⟩ := Proposal.runs source.program fallback n bits
  rcases result with exhausted | ⟨word, consumed, wordSmall, consumedSmall, path⟩
  · refine ⟨2 * fallback.length + 2 + proposalTicks, .exhausted, ?_,
      prepared.executes (bank source.program fallback) (exhausted.executes source.program fallback)⟩
    unfold trialBudget
    omega
  · obtain ⟨ticks, outcome, cost, execution⟩ :=
      source_bounded source fallback n bits word consumed sourceTime (bounded word wordSmall)
    have before := prepared.trans (bank source.program fallback) (path.toSteps _)
    refine ⟨2 * fallback.length + 2 + proposalTicks + ticks, outcome, ?_,
      before.executes (bank source.program fallback) execution⟩
    unfold trialBudget
    omega

/-- Per-word finite termination suffices for finite-seed termination of the
whole generator; the finite word chooser cannot loop. -/
theorem machine_terminates (termination : ∀ word, source.Terminates (decisionData word)) (n : ℕ) :
    (machine source fallback).Terminates (generatorData n) := by
  intro bits
  change ∃ ticks result, (bank source.program fallback).Executes (generatorData n) bits
    (bank source.program fallback).initialConfiguration ticks result
  by_cases short : n < fallback.length
  · obtain ⟨ticks, _, exhausted⟩ := short_index source.program fallback n short bits
    exact ⟨ticks, .exhausted, exhausted⟩
  · have prepared := long_index source.program fallback n (by omega) bits
    obtain ⟨proposalTicks, _, result⟩ := Proposal.runs source.program fallback n bits
    rcases result with exhausted | ⟨word, consumed, wordSmall, consumedSmall, path⟩
    · exact ⟨2 * fallback.length + 2 + proposalTicks, .exhausted,
        prepared.executes (bank source.program fallback) (exhausted.executes source.program fallback)⟩
    · obtain ⟨sourceTicks, result, execution⟩ := termination word (bits.drop consumed)
      obtain ⟨ticks, _, actual⟩ := source_executes source.program fallback n bits word consumed execution
        (Nat.zero_le _)
      have before := prepared.trans (bank source.program fallback) (path.toSteps _)
      exact ⟨2 * fallback.length + 2 + proposalTicks + ticks, sourceOutcome word fallback result,
        before.executes (bank source.program fallback) actual⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
