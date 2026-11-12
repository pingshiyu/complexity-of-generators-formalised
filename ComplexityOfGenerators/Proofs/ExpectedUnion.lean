import ComplexityOfGenerators.Proofs.BoundedPhaseUnion
import ComplexityOfGenerators.Proofs.ExpectedFamilyCriteria

/-! Native expected-time union for EPG and `LayerFastELEPG`.
These normalisation-based constructions use the historical per-layer fast-path
family requirements. Current ELEPG results are developed separately using
direct original-source calls. -/
namespace ComplexityOfGenerators
noncomputable section
variable {α : Type} [Fintype α]

namespace UniformGenerators

theorem language_eq_union_of_layers (R G H : UniformGenerators α)
    (layers : ∀ n, R.layer n = G.layer n ∪ H.layer n) : R.language = G.language ∪ H.language := by
  ext word
  change (∃ n, word ∈ R.layer n) ↔ (∃ n, word ∈ G.layer n) ∨ ∃ n, word ∈ H.layer n
  simp_rw [layers]
  constructor
  · rintro ⟨n, left | right⟩
    · exact Or.inl ⟨n, left⟩
    · exact Or.inr ⟨n, right⟩
  · rintro (⟨n, left⟩ | ⟨n, right⟩)
    · exact ⟨n, Or.inl left⟩
    · exact ⟨n, Or.inr right⟩

theorem union_indexCoverage (R G H : UniformGenerators α)
    (layers : ∀ n, R.layer n = G.layer n ∪ H.layer n)
    (left : G.PolynomialIndexCoverage) (right : H.PolynomialIndexCoverage) : R.PolynomialIndexCoverage := by
  obtain ⟨leftBound, left⟩ := left
  obtain ⟨rightBound, right⟩ := right
  refine ⟨leftBound.add rightBound, fun word member => ?_⟩
  have language := language_eq_union_of_layers R G H layers
  rw [language] at member
  have bound := leftBound.add_le rightBound word.length
  rcases member with member | member
  · obtain ⟨n, small, produced⟩ := left word member
    exact ⟨n, by omega, by rw [layers]; exact Or.inl produced⟩
  · obtain ⟨n, small, produced⟩ := right word member
    exact ⟨n, by omega, by rw [layers]; exact Or.inr produced⟩

end UniformGenerators

theorem epg_union {L K : Language α} (left : L ∈ EPG α) (right : K ∈ EPG α) : L ∪ K ∈ EPG α := by
  obtain ⟨G, leftLanguage, leftExpected⟩ := left
  obtain ⟨H, rightLanguage, rightExpected⟩ := right
  let P := BoundedPhaseFamily.ofExpected G.toUniformGenerators G.expectedLength leftExpected
  let Q := BoundedPhaseFamily.ofExpected H.toUniformGenerators H.expectedLength rightExpected
  let R := (P.union Q).repeated
  apply mem_epg_of_lengthSlices (L ∪ K) R (P.union Q).repeated_expectedPolynomialTime
  intro n
  change (P.union Q).repeated.layer n = _
  rw [BoundedPhaseFamily.repeated_layer, BoundedPhaseFamily.union_layer]
  rw [BoundedPhaseFamily.ofExpected_layer, BoundedPhaseFamily.ofExpected_layer,
    G.layer_eq_lengthSlice, H.layer_eq_lengthSlice, leftLanguage, rightLanguage]
  ext word
  simp [lengthSlice, or_and_right]

theorem layerFastELEPG_union {L K : Language α} (left : L ∈ LayerFastELEPG α) (right : K ∈ LayerFastELEPG α) : L ∪ K ∈ LayerFastELEPG α := by
  obtain ⟨leftInfinite, G, leftLanguage, _, leftMean, leftExpected, leftCoverage⟩ := left
  obtain ⟨_, H, rightLanguage, _, rightMean, rightExpected, rightCoverage⟩ := right
  let P := BoundedPhaseFamily.ofExpected G leftMean leftExpected
  let Q := BoundedPhaseFamily.ofExpected H rightMean rightExpected
  let R := (P.union Q).repeated
  have layers (n : ℕ) : R.layer n = G.layer n ∪ H.layer n := by
    change (P.union Q).repeated.layer n = _
    rw [BoundedPhaseFamily.repeated_layer, BoundedPhaseFamily.union_layer,
      BoundedPhaseFamily.ofExpected_layer, BoundedPhaseFamily.ofExpected_layer]
  have language : R.language = L ∪ K := by
    rw [UniformGenerators.language_eq_union_of_layers R G H layers, leftLanguage, rightLanguage]
  exact mem_layerFastELEPG_of_expected_family (leftInfinite.mono Set.subset_union_left) R language
    (P.union Q).repeated_expectedLength (P.union Q).repeated_expectedPolynomialTime
    (UniformGenerators.union_indexCoverage R G H layers leftCoverage rightCoverage)

end
end ComplexityOfGenerators
