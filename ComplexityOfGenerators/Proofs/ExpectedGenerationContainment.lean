import ComplexityOfGenerators.ExpectedGenerators
import ComplexityOfGenerators.Proofs.PolynomialGenerationContainment

/-!
# Expected polynomial-time exact generation is contained in NP

The fast-path clause of `ExpectedPolynomialTime` supplies polynomially short
accepting runs for individual words.  The existing native generator recognizer and polynomial
clock turn those runs into bounded nondeterministic decision computations.
-/

namespace ComplexityOfGenerators

theorem epg_subset_np {α : Type} [Fintype α] : EPG α ⊆ NP α := by
  rintro L ⟨G, language, p, _runtime, short⟩
  have coverage : ∀ word, word ∈ G.layer word.length ↔ word ∈ L := by
    intro word
    rw [G.layer_eq_lengthSlice, language]
    simp [lengthSlice]
  apply mem_np_of_polynomial_layer_witnesses L G.toUniformGenerators coverage p
  intro word member
  obtain ⟨bits, _, execution⟩ := short word.length word member
  exact ⟨bits, execution⟩

/-- Proposition 5.2 of the current manuscript. -/
theorem pg_subset_epg_subset_np {α : Type} [Fintype α] :
    PG α ⊆ EPG α ∧ EPG α ⊆ NP α :=
  ⟨pg_subset_epg, epg_subset_np⟩

end ComplexityOfGenerators
