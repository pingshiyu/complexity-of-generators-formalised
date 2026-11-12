import ComplexityOfGenerators.MultitapeComplexityClasses
import ComplexityOfGenerators.Simulation.TransducerBank.Native.Semantics

namespace ComplexityOfGenerators.Simulation.TransducerBank.Native

noncomputable section

variable {α : Type} [Fintype α]

/-- The same exact generator, embedded in the genuine one-tape bank. -/
def generatorFamily (G : GeneratorFamily α) : Multitape.GeneratorFamily α where
  machine := machine G.machine
  isGenerator := fun n => isGenerator G.machine (generatorData n) (G.isGenerator n)
  outputLength := by
    intro n word member
    apply G.outputLength n word
    change word ∈ (machine G.machine).generatedLanguage (generatorData n) at member
    rw [generatedLanguage G.machine (generatorData n) (G.isGenerator n).1.1] at member
    exact member

theorem generatorFamily_layer (G : GeneratorFamily α) (n : ℕ) :
    (generatorFamily G).toUniformGenerators.layer n = G.toUniformGenerators.layer n :=
  generatedLanguage G.machine (generatorData n) (G.isGenerator n).1.1

theorem generatorFamily_language (G : GeneratorFamily α) :
    (generatorFamily G).toUniformGenerators.language = G.toUniformGenerators.language := by
  ext word
  exact exists_congr fun n => Set.ext_iff.mp (generatorFamily_layer G n) word

/-- Native exact time classes embed with no transition overhead. This does not
supply the subsequent ordinary-input clocked recognition theorem. -/
theorem gtime_subset_multitape_gtime (time : ℕ → ℕ) :
    ComplexityOfGenerators.GTIME α time ⊆ Multitape.GTIME α time := by
  rintro language ⟨G, generated, bounded⟩
  refine ⟨generatorFamily G, ?_, ?_⟩
  · rw [generatorFamily_language, generated]
  · intro n
    exact acceptingTimeBound G.machine (generatorData n) (G.isGenerator n).1.1
      (time n) (bounded n)

end
end ComplexityOfGenerators.Simulation.TransducerBank.Native
