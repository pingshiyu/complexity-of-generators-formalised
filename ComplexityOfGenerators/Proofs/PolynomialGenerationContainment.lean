import ComplexityOfGenerators.Proofs.ResourceGeneration

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
  have member := (generatorRecognizer_accepts_iff_layer G.toUniformGenerators w).mp
    ⟨bits, accepted⟩
  exact ⟨w.length, member⟩

/-- The non-strict containment in Theorem 5.1, proved for every finite alphabet
without any cryptographic assumption. -/
theorem pg_subset_np {α : Type} [Fintype α] : PG α ⊆ NP α := by
  rintro L ⟨G, language, bounded⟩
  apply mem_np_of_polynomial_layer_generation L G.toUniformGenerators ?_
    bounded.acceptingPolynomialTime
  intro word
  rw [G.layer_eq_lengthSlice, language]
  simp [lengthSlice]

end ComplexityOfGenerators
