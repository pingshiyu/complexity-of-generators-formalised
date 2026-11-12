import ComplexityOfGenerators.Proofs.ResourceGenerationSpace

/-! The exact-slice specialisation of the common polynomial-space recognition
construction. All machine translations and visited-cell bounds are shared with
the up-to-size result. -/

namespace ComplexityOfGenerators
variable {α : Type} [Fintype α]

/-- Exact polynomial-space generation is contained in polynomial-space decision. -/
theorem pspaceg_subset_pspace : PSPACEG α ⊆ PSPACE α := by
  rintro L ⟨G, language, bounded⟩
  apply mem_pspace_of_polynomial_layer_generation L G.toUniformGenerators ?_ bounded
  intro word
  rw [G.layer_eq_lengthSlice, language]
  simp [lengthSlice]

end ComplexityOfGenerators
