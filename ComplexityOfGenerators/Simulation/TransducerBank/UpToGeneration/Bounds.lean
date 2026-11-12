import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Execution

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

/-- Empty short slices have no deadline obligation; every other accepted branch
is bounded by the actual proposal/source/replay execution. -/
theorem machine_acceptingTimeBound (n sourceTime : ℕ)
    (bounded : ∀ word, word.length ≤ n → source.TimeBound (decisionData word) sourceTime) :
    (machine source fallback).AcceptingTimeBound (generatorData n) (trialBudget fallback n sourceTime) := by
  intro bits ticks word accepted
  by_cases short : n < fallback.length
  · exact False.elim ((short_no_accepts source fallback n short bits) ⟨word, ticks, accepted⟩)
  · obtain ⟨actualTicks, result, cost, execution⟩ :=
      long_timeBound source fallback n (by omega) sourceTime bounded bits
    have same := (TapeBank.Executes.unique (bank source.program fallback) accepted execution).1
    exact same ▸ cost

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
