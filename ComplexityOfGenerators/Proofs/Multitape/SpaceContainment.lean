import ComplexityOfGenerators.Proofs.Multitape.IndexedSpaceRecognition
import ComplexityOfGenerators.Proofs.Multitape.GeneratorLayers
import ComplexityOfGenerators.Proofs.Multitape.SpaceResources
import ComplexityOfGenerators.Proofs.Multitape.SpaceConverse

/-! General space-bounded generators are recognised by actual finite
multitape deciders. Unary size information is represented by logarithmic
binary counters, and a charged space constructor supplies the real clock. -/

namespace ComplexityOfGenerators.Multitape

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

/-- The SPACE half of Proposition 4.1, with total work-cell source bounds. -/
theorem gspace_subset_nspace (space : ℕ→ℕ) (constructible : SpaceConstructible space)
    (dominates : ∀ n,Nat.log 2 n<space n) : GSPACE α space⊆NSPACE α space := by
  rintro language ⟨family,generated,bounded⟩
  apply indexed_output_mem_nspace language family.machine space space constructible
    (ResourceOrder.refl space) (ResourceOrder.logarithm dominates)
    (eventually_positive_of_logarithm dominates)
    (fun n => (family.isGenerator n).1.1)
  · intro n
    exact family.machine.radiusSpaceBound_of_cells (generatorData n) (space n) (bounded n)
  · intro word
    rw [← family.machine.generatedLanguage_iff_produces (generatorData word.length) word]
    change word∈family.toUniformGenerators.layer word.length ↔ word∈language
    rw [family.input_length_layer,generated]

private theorem logarithm_order_of_linear (space : ℕ→ℕ) (dominates : ∀ n,n≤space n) :
    ResourceOrder (fun n => Nat.clog 2 (n+1)) space := by
  refine ⟨1,0,by decide,?_⟩
  intro n _
  have power : n < 2^n := Nat.lt_two_pow_self
  have digits : Nat.clog 2 (n+1)≤n := Nat.clog_le_of_le_pow (by omega)
  simpa only [Nat.one_mul] using digits.trans (dominates n)

/-- The forward SPACE half of Proposition 4.2. Its linear lower bound also
allows s(0)=0; positivity is needed only eventually in the O(s) convention. -/
theorem gspaceUpTo_subset_nspace (space : ℕ→ℕ) (constructible : SpaceConstructible space)
    (dominates : ∀ n,n≤space n) : GSPACEUpTo α space⊆NSPACE α space := by
  rintro language ⟨family,workspace,generated,order,bounded⟩
  apply indexed_output_mem_nspace language family.machine workspace space constructible order
    (logarithm_order_of_linear space dominates)
    ⟨1,fun n large => large.trans (dominates n)⟩
    (fun n => (family.isGenerator n).1.1)
  · intro n
    exact family.machine.radiusSpaceBound_of_cells (generatorData n) (workspace n) (bounded n)
  · intro word
    rw [← family.machine.generatedLanguage_iff_produces (generatorData word.length) word]
    change word∈family.toUniformGenerators.layer word.length ↔ word∈language
    rw [family.input_length_layer,generated]

/-- The SPACE characterisation in Proposition 4.2, on the fixed finite
multitape model with actual total visited work-cell bounds. -/
theorem gspaceUpTo_eq_nspace (space : ℕ→ℕ) (constructible : SpaceConstructible space)
    (monotone : Monotone space) (dominates : ∀ n,n≤space n) :
    GSPACEUpTo α space=NSPACE α space :=
  Set.Subset.antisymm (gspaceUpTo_subset_nspace space constructible dominates)
    (nspace_subset_gspaceUpTo space monotone dominates)

end
end ComplexityOfGenerators.Multitape
