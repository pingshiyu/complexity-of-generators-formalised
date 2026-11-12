import ComplexityOfGenerators.Simulation.NativeNTM.Space
import ComplexityOfGenerators.Proofs.LibrarySpace
import ComplexityOfGenerators.Foundations.BoundedGeneration

/-!
# Polynomial-space recognition of length-indexed generator layers

The construction does not require exact output lengths.  It compares output
with the input as it is emitted, then uses the verified native/library space
translations and the library's terminating bounded-reachability algorithm.
-/

namespace ComplexityOfGenerators
open Simulation
noncomputable section
variable {α : Type} [Fintype α]

/-- A uniformly polynomial-space generator whose input-length layer contains
exactly the input-language members supplies a native polynomial-space decider. -/
theorem mem_pspace_of_polynomial_layer_generation (L : Language α) (G : UniformGenerators α)
    (coverage : ∀ word, word ∈ G.layer word.length ↔ word ∈ L)
    (resources : G.PolynomialSpace) : L ∈ PSPACE α := by
  obtain ⟨space, bounded⟩ := resources
  let R := outputMatcher G.machine
  have matcherBound (word : List α) : R.SpaceBound (NativeNTM.sourceData word) (space word.length) :=
    outputMatcher_spaceBound G.machine (NativeNTM.sourceData word) (space word.length) (bounded word.length)
  have decider := standard_pspace_encoded_preimage (α := α)
    (NativeNTM.language_mem_PSPACE R space matcherBound)
  have same : {word : List α | NativeNTM.encode word ∈ NativeNTM.language R} = L := by
    ext word
    rw [Set.mem_ofPred_eq, NativeNTM.encoded_mem_iff R word (space word.length) (matcherBound word)]
    simp only [R, outputMatcher_accepts_iff]
    change (∃ bits, G.machine.Produces (generatorData word.length) bits word) ↔ word ∈ L
    rw [← G.machine.mem_generatedLanguage_iff_produces]
    exact coverage word
  rwa [same] at decider


end
end ComplexityOfGenerators
