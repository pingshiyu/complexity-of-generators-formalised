import ComplexityOfGenerators.MultitapeComplexityClasses
import ComplexityOfGenerators.Simulation.TransducerBank.AcceptedRandomTape

namespace ComplexityOfGenerators.Multitape

variable {α : Type} [Fintype α]

theorem GeneratorFamily.layer_eq_slice (G : GeneratorFamily α) (n : ℕ) :
    G.toUniformGenerators.layer n = lengthSlice G.toUniformGenerators.language n := by
  ext word
  constructor
  · intro member
    exact ⟨⟨n, member⟩, G.outputLength n word member⟩
  · rintro ⟨⟨index, member⟩, length⟩
    have actual := G.outputLength index word member
    have same : index = n := by omega
    simpa only [same] using member

theorem GeneratorFamily.input_length_layer (G : GeneratorFamily α) (word : Word α) :
    word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ G.toUniformGenerators.language := by
  rw [G.layer_eq_slice]
  simp [lengthSlice]

theorem UpToGeneratorFamily.input_length_layer (G : UpToGeneratorFamily α) (word : Word α) :
    word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ G.toUniformGenerators.language := by
  rw [G.prefixLanguage]
  simp

end ComplexityOfGenerators.Multitape
