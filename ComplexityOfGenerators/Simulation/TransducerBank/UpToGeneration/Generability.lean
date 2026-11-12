import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Execution
import ComplexityOfGenerators.Proofs.Multitape.GeneratorCriteria
import ComplexityOfGenerators.Proofs.Multitape.FiniteInputBounds

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

/-- A real all-branch decider yields genuine generators at every index. Empty
short indices drain; all other indices accept every infinite coin stream. The
finite input maximum is used only in this proof, never by the program. -/
theorem machine_isGenerator (termination : ∀ word, ∃ time, source.TimeBound (decisionData word) time)
    (n : ℕ) : (machine source fallback).IsGenerator (generatorData n) := by
  by_cases short : n < fallback.length
  · have finite : ∀ word, source.Terminates (decisionData word) := by
      intro word bits
      obtain ⟨time, bounded⟩ := termination word
      obtain ⟨ticks, result, _, execution⟩ := bounded bits
      exact ⟨ticks, result, execution⟩
    exact (machine source fallback).isGenerator_of_empty (generatorData n)
      ⟨machine_terminates source fallback finite n, noRejected source fallback n⟩
      (short_no_accepts source fallback n short)
  · obtain ⟨time, bounded⟩ := Multitape.finite_input_timeBound source termination n
    exact (machine source fallback).isGenerator_of_timeBound (generatorData n)
      (trialBudget fallback n time) (long_timeBound source fallback n (by omega) time bounded)
      (noRejected source fallback n)

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
