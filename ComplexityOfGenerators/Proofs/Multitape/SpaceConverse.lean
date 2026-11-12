import ComplexityOfGenerators.Proofs.Multitape.UpToFamily
import ComplexityOfGenerators.Proofs.Multitape.MonotoneEnvelopes
import ComplexityOfGenerators.Proofs.Multitape.UpToResourceBounds
import ComplexityOfGenerators.Proofs.Multitape.UpToElementarySpace
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Space
import ComplexityOfGenerators.MultitapeSpaceClasses

/-! The same concrete proposal/source/fallback generator preserves space.
The guessed word occupies a real extra tape, source work remains separate, and
all prefixes stay inside one region independent of source running time. The
fixed-bank radius is converted to actual total visited work cells. -/

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

open Simulation.TransducerBank.UpToGeneration

variable {α : Type} [Fintype α]

theorem nspace_subset_gspaceUpTo (space : ℕ → ℕ) (monotone : Monotone space)
    (dominates : ∀ n, n ≤ space n) : NSPACE α space ⊆ GSPACEUpTo α space := by
  classical
  intro language member
  by_cases nonempty : language.Nonempty
  · obtain ⟨source, workspace, order, termination, bounded, recognizes⟩ := member
    have lengths : ∃ n, ∃ word ∈ language, word.length = n := by
      obtain ⟨word, inLanguage⟩ := nonempty
      exact ⟨word.length, word, inLanguage, rfl⟩
    obtain ⟨fallback, fallbackMember, fallbackLength⟩ := Nat.find_spec lengths
    have shortest : ∀ word ∈ language, fallback.length ≤ word.length := by
      intro word inLanguage
      rw [fallbackLength]
      exact Nat.find_min' lengths ⟨word, inLanguage, rfl⟩
    obtain ⟨copies, positive, envelope⟩ :=
      monotone_space_envelope source workspace space order monotone bounded
    let family := upToFamily language source fallback termination recognizes fallbackMember shortest
    let generator := machine source fallback
    let radius (n : ℕ) := totalRadius fallback n (copies * (space n + 1))
    let cells (n : ℕ) := 2 * generator.tapes * radius n + generator.tapes
    have eventualPositive : ∃ threshold, ∀ n, threshold ≤ n → 1 ≤ space n :=
      ⟨1, fun n large => large.trans (dominates n)⟩
    have radiusOrder : ResourceOrder radius space := upTo_spaceRadius_order fallback copies space dominates
    refine ⟨family, cells,
      upToFamily_language language source fallback termination recognizes fallbackMember shortest,
      radiusOrder.affine eventualPositive (2 * generator.tapes) generator.tapes, ?_⟩
    intro n
    have finite : ∀ word, source.Terminates (decisionData word) := by
      intro word bits
      obtain ⟨time, bound⟩ := termination word
      obtain ⟨ticks, result, _, execution⟩ := bound bits
      exact ⟨ticks, result, execution⟩
    have nativeRadius : generator.SpaceBound (generatorData n) (radius n) :=
      machine_spaceBound source fallback finite n (copies * (space n + 1)) (envelope n)
    have nativeCells := generator.cellSpaceBound_of_radius (generatorData n) (radius n) nativeRadius
    change generator.CellSpaceBound (generatorData n) (cells n)
    convert nativeCells using 1 <;> dsimp [cells] <;> ring
  · have empty : language = ∅ := Set.not_nonempty_iff_eq_empty.mp nonempty
    simpa only [empty] using (empty_mem_gspaceUpTo (α := α) space dominates)

end
end ComplexityOfGenerators.Multitape
