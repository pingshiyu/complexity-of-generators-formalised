import ComplexityOfGenerators.Proofs.ResourceGeneration

/-!
# Polynomial-time generation is contained in NP

The proof uses exact-length slices and a recognizer compiled into the native
machine model. The internal family interface supplies separate seed and execution
budgets; the accepting-time bridge relates these to the paper's bounds on
accepting runs. A polynomial clock stops every recognizer branch, including
long seeds on empty slices, and full-budget seeds supply accepting witnesses.
-/

namespace ComplexityOfGenerators

theorem generatorRecognizer_sound {α : Type} [Fintype α] (G : GeneratorFamily α)
    (w : List α) (bits : BitString)
    (accepted : (Simulation.generatorRecognizer G.machine).Accepts (decisionData w) bits) :
    w ∈ G.toUniformGenerators.language := by
  have member := (generatorRecognizer_accepts_iff_layer G.toUniformGenerators w).mp
    ⟨bits, accepted⟩
  exact ⟨w.length, member⟩

/-- The PG-to-NP containment, proved for every finite alphabet
without any cryptographic assumption. -/
theorem pg_subset_np {α : Type} [Fintype α] : PG α ⊆ NP α := by
  rintro L ⟨G, language, bounded⟩
  apply mem_np_of_polynomial_layer_generation L G.toUniformGenerators ?_
    bounded.acceptingPolynomialTime
  intro word
  rw [G.layer_eq_lengthSlice, language]
  simp [lengthSlice]

end ComplexityOfGenerators
