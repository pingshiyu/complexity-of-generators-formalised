import ComplexityOfGenerators.Proofs.PolynomialStarWitnesses
import ComplexityOfGenerators.Proofs.PolynomialStarProductivity
import ComplexityOfGenerators.Simulation.StarGenerator.Execution

/-! A native polynomial generator for Kleene star, including empty slices and ε. -/

namespace ComplexityOfGenerators

open Simulation.StarGenerator Simulation.WordStack
noncomputable section

variable {α : Type} [Fintype α]

/-- The Kleene star clause of current Proposition 6.3 for PG. The finite controller,
its primitive costs, and its actual compilation to a native machine are proved. -/
theorem pg_star {L : Language α} (member : L ∈ PG α) : IndexedSupport.star L ∈ PG α := by
  obtain ⟨F, language, sourceSeed, sourceTime, bounded⟩ := member
  subst L
  let seed := starSeed sourceSeed
  apply Command.mem_pg
    (command F.machine sourceSeed sourceTime seed) 0
    (IndexedSupport.star F.toUniformGenerators.language) seed
    (stackTime F.machine sourceSeed sourceTime seed)
    (commandValue F.machine sourceSeed sourceTime seed)
  · intro n bits
    obtain ⟨t, _, result, run, output⟩ := command_runs F.machine sourceSeed sourceTime seed n _
      (budgetConditions sourceSeed sourceTime seed n) bits
    exact ⟨t, result, run, output⟩
  · intro n bits word output
    unfold commandValue at output
    split at output
    · exact algorithm_sound sourceSeed sourceTime F n _ word output
    · simp at output
  · intro n word member
    obtain ⟨bits, length, generated⟩ := algorithm_complete F sourceSeed sourceTime bounded n word member
    refine ⟨bits, length, ?_⟩
    change bits.length = seed n at length
    simp only [commandValue, ← length, le_refl, ite_true, List.take_length]
    exact generated
  · intro n bits length nonempty
    have generated := algorithm_productive F sourceSeed sourceTime bounded n bits length nonempty
    simpa only [commandValue, ← length, le_refl, ite_true, List.take_length] using generated
  · intro n bits length
    exact command_time F.machine sourceSeed sourceTime seed n bits length

end
end ComplexityOfGenerators
