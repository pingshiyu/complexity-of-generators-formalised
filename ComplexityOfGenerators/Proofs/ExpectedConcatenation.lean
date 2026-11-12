import ComplexityOfGenerators.Proofs.BoundedPhaseConcatenation
import ComplexityOfGenerators.Proofs.ExpectedFamilyCriteria

/-! Native expected-time concatenation for EPG and `LayerFastELEPG`.
These normalisation-based constructions use the historical per-layer fast-path
family requirements. Current ELEPG results are developed separately using
direct original-source calls. -/
namespace ComplexityOfGenerators
noncomputable section
variable {α : Type} [Fintype α]

namespace UniformGenerators

theorem language_eq_concat_of_layers (R G H : UniformGenerators α)
    (layers : ∀ n, R.layer n = IndexedSupport.concatLayers G.layer H.layer n) :
    R.language = IndexedSupport.concat G.language H.language := by
  change IndexedSupport.language R.layer = IndexedSupport.concat
    (IndexedSupport.language G.layer) (IndexedSupport.language H.layer)
  rw [show R.layer = IndexedSupport.concatLayers G.layer H.layer from funext layers,
    IndexedSupport.concat_language]

theorem concat_indexCoverage (R G H : UniformGenerators α)
    (layers : ∀ n, R.layer n = IndexedSupport.concatLayers G.layer H.layer n)
    (left : G.PolynomialIndexCoverage) (right : H.PolynomialIndexCoverage) : R.PolynomialIndexCoverage := by
  obtain ⟨leftBound, left⟩ := left
  obtain ⟨rightBound, right⟩ := right
  refine ⟨leftBound.add rightBound, fun word member => ?_⟩
  rw [language_eq_concat_of_layers R G H layers] at member
  obtain ⟨u, leftMember, v, rightMember, rfl⟩ := member
  obtain ⟨i, smallLeft, generatedLeft⟩ := left u leftMember
  obtain ⟨j, smallRight, generatedRight⟩ := right v rightMember
  refine ⟨i+j, ?_, ?_⟩
  · exact (Nat.add_le_add
      (smallLeft.trans (leftBound.monotone (by simp)))
      (smallRight.trans (rightBound.monotone (by simp)))).trans (leftBound.add_le rightBound (u++v).length)
  · rw [layers]
    exact ⟨i, j, rfl, u, generatedLeft, v, generatedRight, rfl⟩

end UniformGenerators

namespace IndexedSupport

theorem concat_lengthSlices (L K : Language α) (n : ℕ) :
    concatLayers (lengthSlice L) (lengthSlice K) n = lengthSlice (concat L K) n := by
  ext word
  constructor
  · rintro ⟨i, j, sum, u, ⟨left, leftLength⟩, v, ⟨right, rightLength⟩, rfl⟩
    exact ⟨⟨u, left, v, right, rfl⟩, by simp [List.length_append, leftLength, rightLength, sum]⟩
  · rintro ⟨⟨u, left, v, right, rfl⟩, length⟩
    refine ⟨u.length, v.length, ?_, u, ⟨left, rfl⟩, v, ⟨right, rfl⟩, rfl⟩
    simpa only [List.length_append] using length

theorem concat_infinite_left {L K : Language α} (infinite : L.Infinite) (nonempty : K.Nonempty) :
    (concat L K).Infinite := by
  obtain ⟨v, member⟩ := nonempty
  have injective : Function.Injective (fun u : List α => u ++ v) := by
    intro u w equal
    exact List.append_cancel_right equal
  exact (infinite.image injective.injOn).mono (by
    rintro word ⟨u, left, equal⟩
    exact ⟨u, left, v, member, equal⟩)

end IndexedSupport

theorem epg_concatenation {L K : Language α} (left : L ∈ EPG α) (right : K ∈ EPG α) :
    IndexedSupport.concat L K ∈ EPG α := by
  obtain ⟨G, leftLanguage, leftExpected⟩ := left
  obtain ⟨H, rightLanguage, rightExpected⟩ := right
  let P := BoundedPhaseFamily.ofExpected G.toUniformGenerators G.expectedLength leftExpected
  let Q := BoundedPhaseFamily.ofExpected H.toUniformGenerators H.expectedLength rightExpected
  let R := (P.concatenate Q).repeated
  apply mem_epg_of_lengthSlices (IndexedSupport.concat L K) R (P.concatenate Q).repeated_expectedPolynomialTime
  intro n
  change (P.concatenate Q).repeated.layer n = _
  rw [BoundedPhaseFamily.repeated_layer, BoundedPhaseFamily.concatenate_layer]
  have leftLayers : P.layer = lengthSlice L := by
    funext i
    rw [BoundedPhaseFamily.ofExpected_layer, G.layer_eq_lengthSlice, leftLanguage]
  have rightLayers : Q.layer = lengthSlice K := by
    funext i
    rw [BoundedPhaseFamily.ofExpected_layer, H.layer_eq_lengthSlice, rightLanguage]
  rw [leftLayers, rightLayers, IndexedSupport.concat_lengthSlices]

theorem layerFastELEPG_concatenation {L K : Language α} (left : L ∈ LayerFastELEPG α) (right : K ∈ LayerFastELEPG α) :
    IndexedSupport.concat L K ∈ LayerFastELEPG α := by
  obtain ⟨leftInfinite, G, leftLanguage, _, leftMean, leftExpected, leftCoverage⟩ := left
  obtain ⟨rightInfinite, H, rightLanguage, _, rightMean, rightExpected, rightCoverage⟩ := right
  let P := BoundedPhaseFamily.ofExpected G leftMean leftExpected
  let Q := BoundedPhaseFamily.ofExpected H rightMean rightExpected
  let R := (P.concatenate Q).repeated
  have layers (n : ℕ) : R.layer n = IndexedSupport.concatLayers G.layer H.layer n := by
    change (P.concatenate Q).repeated.layer n = _
    rw [BoundedPhaseFamily.repeated_layer, BoundedPhaseFamily.concatenate_layer]
    have leftLayers : P.layer = G.layer := funext (BoundedPhaseFamily.ofExpected_layer G leftMean leftExpected)
    have rightLayers : Q.layer = H.layer := funext (BoundedPhaseFamily.ofExpected_layer H rightMean rightExpected)
    rw [leftLayers, rightLayers]
  have language : R.language = IndexedSupport.concat L K := by
    rw [UniformGenerators.language_eq_concat_of_layers R G H layers, leftLanguage, rightLanguage]
  exact mem_layerFastELEPG_of_expected_family (IndexedSupport.concat_infinite_left leftInfinite rightInfinite.nonempty) R language
    (P.concatenate Q).repeated_expectedLength (P.concatenate Q).repeated_expectedPolynomialTime
    (UniformGenerators.concat_indexCoverage R G H layers leftCoverage rightCoverage)

end
end ComplexityOfGenerators
