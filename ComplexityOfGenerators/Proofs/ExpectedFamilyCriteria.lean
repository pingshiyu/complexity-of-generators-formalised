import ComplexityOfGenerators.ExpectedGenerators
import ComplexityOfGenerators.Foundations.BoundedGeneration

/-! Package implemented expected-time families without repeating their exact
length and total-language arguments in every closure construction. -/
namespace ComplexityOfGenerators
variable {α : Type} [Fintype α]

theorem UniformGenerators.language_eq_of_layers_eq (G H : UniformGenerators α)
    (layers : ∀ n, G.layer n = H.layer n) : G.language = H.language := by
  ext word
  change (∃ n, word ∈ G.layer n) ↔ ∃ n, word ∈ H.layer n
  simp only [layers]

theorem mem_epg_of_lengthSlices (L : Language α) (G : UniformGenerators α)
    (expected : G.ExpectedPolynomialTime) (layers : ∀ n, G.layer n = lengthSlice L n) : L ∈ EPG α := by
  let exactFamily : GeneratorFamily α := {
    machine := G.machine
    isGenerator := G.isGenerator
    outputLength := by
      intro n word member
      change word ∈ G.layer n at member
      rw [layers n] at member
      exact member.2 }
  refine ⟨exactFamily, ?_, expected⟩
  ext word
  change (∃ n, word ∈ G.layer n) ↔ word ∈ L
  simp only [layers]
  exact ⟨fun ⟨_, member, _⟩ => member, fun member => ⟨word.length, member, rfl⟩⟩

end ComplexityOfGenerators
