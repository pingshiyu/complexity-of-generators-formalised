import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition
import ComplexityOfGenerators.Simulation.GeneratorRecognizerCorrectness

/-!
# Polynomial-time generation is contained in NP

The proof uses the paper's exact-length slices and the approved separate seed
and execution bounds. The verifier is compiled into the original native machine
model. A polynomial clock stops every branch, including long seeds on empty
slices, while the full-budget seed lemma supplies accepting witnesses.
-/

namespace ComplexityOfGenerators

theorem generatorRecognizer_sound {α : Type} [Fintype α] (G : GeneratorFamily α)
    (w : List α) (bits : BitString)
    (accepted : (Simulation.generatorRecognizer G.machine).Accepts (decisionData w) bits) :
    w ∈ G.toUniformGenerators.language := by
  classical
  obtain ⟨out, acceptedTime, accepts⟩ := accepted
  obtain ⟨time, result, halted⟩ := (G.isGenerator w.length).1.1 bits
  have simulated := Simulation.generatorRecognizer_run G.machine w bits time result halted
  have same := (Simulation.generatorRecognizer G.machine).halted_outcome_unique (decisionData w) bits
    acceptedTime _ (.accepted out) (Simulation.matcherOutcome w result) accepts simulated
  cases result with
  | rejected => simp [Simulation.matcherOutcome] at same
  | exhausted => simp [Simulation.matcherOutcome] at same
  | accepted v =>
      have word : v = w := by
        by_contra different
        simp [Simulation.matcherOutcome, different] at same
      subst v
      refine ⟨w.length, bits ++ [false], by simp, ?_⟩
      exact G.machine.produces_append (generatorData w.length) bits [false] w ⟨time, halted⟩

/-- The non-strict containment in Theorem 5.1, proved for every finite alphabet
without any cryptographic assumption. -/
theorem pg_subset_np {α : Type} [Fintype α] : PG α ⊆ NP α := by
  rintro L member
  obtain ⟨G, language, seed, time, bound⟩ := member
  apply np_of_bounded_acceptance L (Simulation.generatorRecognizer G.machine) (Simulation.generatorRecognizerTime time)
  · intro w bits accepted
    rw [← language]
    exact generatorRecognizer_sound G w bits accepted
  · intro w member
    have layer := G.layer_eq_lengthSlice w.length
    rw [language] at layer
    have inLayer : w ∈ G.toUniformGenerators.layer w.length := by
      rw [layer]
      exact ⟨member, rfl⟩
    obtain ⟨bits, _, execution⟩ := (G.machine.generatedLanguage_iff_budget_seed (generatorData w.length)
      (seed w.length) (time w.length) (seed.positive w.length) (bound w.length) w).mp inLayer
    exact ⟨bits, [], Simulation.generatorRecognizer_accepts_at_bound G.machine time w bits execution⟩

end ComplexityOfGenerators
