import ComplexityOfGenerators.Simulation.NativeNTM.Space
import ComplexityOfGenerators.Proofs.LibrarySpace
import ComplexityOfGenerators.Foundations.BoundedGeneration

/-! The forward direction of Theorem 6.1 uses space-preserving machine
translations and Complexitylib's Savitch decider. The translated recognizer may
loop; the library's finite configuration search still terminates. -/

namespace ComplexityOfGenerators
open Simulation
noncomputable section
variable {α : Type} [Fintype α]

/-- Streaming output comparison, library Savitch reachability, and the verified
return compiler give a native decider over the original finite alphabet.
Neither random-tape length nor running time needs a polynomial bound. -/
theorem pspaceg_subset_pspace : PSPACEG α ⊆ PSPACE α := by
  intro L member
  obtain ⟨G, language, space, bounded⟩ := member
  let R := outputMatcher G.machine
  have matcherBound (word : List α) : R.SpaceBound (NativeNTM.sourceData word) (space word.length) :=
    outputMatcher_spaceBound G.machine (NativeNTM.sourceData word) (space word.length) (bounded word.length)
  have decider := standard_pspace_encoded_preimage (α := α)
    (NativeNTM.language_mem_PSPACE R space matcherBound)
  have same : {word : List α | NativeNTM.encode word ∈ NativeNTM.language R} = L := by
    ext word
    rw [Set.mem_setOf_eq, NativeNTM.encoded_mem_iff R word (space word.length) (matcherBound word)]
    simp only [R, outputMatcher_accepts_iff]
    change (∃ bits, G.machine.Produces (generatorData word.length) bits word) ↔ word ∈ L
    have generated : (∃ bits, G.machine.Produces (generatorData word.length) bits word) ↔
        word ∈ G.machine.generatedLanguage (generatorData word.length) := by
      constructor
      · rintro ⟨bits, produced⟩
        exact ⟨bits ++ [false], by simp, G.machine.produces_append _ bits [false] word produced⟩
      · rintro ⟨bits, _, produced⟩
        exact ⟨bits, produced⟩
    rw [generated]
    change word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ L
    rw [G.layer_eq_lengthSlice, language]
    exact ⟨fun member => member.1, fun member => ⟨member, rfl⟩⟩
  rwa [same] at decider

end
end ComplexityOfGenerators
