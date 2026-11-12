import ComplexityOfGenerators.Proofs.PolynomialConcatenationWitnesses
import ComplexityOfGenerators.Proofs.PolynomialConcatenationProductivity
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Execution

/-! A native polynomial generator for concatenation, including empty slices and ε. -/

namespace ComplexityOfGenerators

open Simulation.ConcatenationGenerator Simulation.WordStack
noncomputable section

variable {α : Type} [Fintype α]

/-- The concatenation clause of current Proposition 6.3 for PG. The finite controller,
its primitive costs, and its actual compilation to a native machine are proved. -/
theorem pg_concatenation {L K : Language α} (left : L ∈ PG α) (right : K ∈ PG α) : IndexedSupport.concat L K ∈ PG α := by
  obtain ⟨G, leftLanguage, leftSeed, leftTime, leftBound⟩ := left
  obtain ⟨H, rightLanguage, rightSeed, rightTime, rightBound⟩ := right
  subst L
  subst K
  let seed := concatSeed leftSeed rightSeed
  apply Command.mem_pg
    (command G.machine H.machine leftSeed leftTime rightSeed rightTime seed) 0
    (IndexedSupport.concat G.toUniformGenerators.language H.toUniformGenerators.language) seed
    (stackTime G.machine H.machine leftSeed leftTime rightSeed rightTime seed)
    (commandValue G.machine H.machine leftSeed leftTime rightSeed rightTime seed)
  · intro n bits
    obtain ⟨t, _, result, run, output⟩ := command_runs G.machine H.machine leftSeed leftTime rightSeed rightTime seed n _
      (budgetConditions leftSeed leftTime rightSeed rightTime seed n) bits
    exact ⟨t, result, run, output⟩
  · intro n bits word output
    unfold commandValue at output
    split at output
    · exact algorithm_sound G H leftSeed leftTime rightSeed rightTime n _ word output
    · simp at output
  · intro n word member
    obtain ⟨bits, length, generated⟩ := algorithm_complete G H leftSeed leftTime rightSeed rightTime
      leftBound rightBound n word member
    refine ⟨bits, length, ?_⟩
    change bits.length = seed n at length
    simp only [commandValue, ← length, le_refl, ite_true, List.take_length]
    exact generated
  · intro n bits length nonempty
    have generated := algorithm_productive G H leftSeed leftTime rightSeed rightTime leftBound rightBound n bits length nonempty
    simpa only [commandValue, ← length, le_refl, ite_true, List.take_length] using generated
  · intro n bits length
    exact command_time G.machine H.machine leftSeed leftTime rightSeed rightTime seed n bits length

end
end ComplexityOfGenerators
