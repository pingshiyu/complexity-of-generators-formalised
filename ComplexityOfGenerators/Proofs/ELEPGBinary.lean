import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Support
import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Fast
import ComplexityOfGenerators.Proofs.OriginalBinaryNativeProperties
import ComplexityOfGenerators.Proofs.OriginalSourceFamilyCriteria
import ComplexityOfGenerators.Proofs.ExpectedUnion
import ComplexityOfGenerators.Proofs.ExpectedConcatenation

/-! Union and concatenation for the current ELEPG definition. The native
machines call the original sources, preserving their full indexed support;
only the global word-length lucky paths are used to obtain fast witnesses. -/
namespace ComplexityOfGenerators
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Simulation MeasureTheory
open scoped ENNReal
variable {α : Type} [Fintype α]

namespace ExpectedOriginalBinarySampling
variable (families : Bool→UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

theorem native_available_of_member (operation : OriginalBinarySelector.Operation) (n : ℕ) (word : List α)
    (member : word∈(OriginalBinaryGenerator.machine families p operation).generatedLanguage (generatorData n)) :
    Available families operation n := by
  have supported := OriginalBinaryGenerator.machine_language_subset families p operation n member
  cases operation with
  | union =>
      rcases supported with left|right
      · exact ⟨false,word,left⟩
      · exact ⟨true,word,right⟩
  | concatenation =>
      obtain ⟨i,j,total,u,left,v,right,equal⟩ := supported
      refine ⟨i,by omega,⟨u,left⟩,?_⟩
      have index : n-i=j := by omega
      rw [index]
      exact ⟨v,right⟩

include expected in
theorem native_isGenerator (operation : OriginalBinarySelector.Operation) (n : ℕ) :
    (OriginalBinaryGenerator.machine families p operation).IsGenerator (generatorData n) := by
  refine ⟨OriginalBinaryGenerator.machine_halting families p operation n,?_⟩
  by_cases active : ((OriginalBinaryGenerator.machine families p operation).generatedLanguage (generatorData n)).Nonempty
  · obtain ⟨word,member⟩ := active
    exact Or.inl (native_productive families p expected operation n
      (native_available_of_member families p operation n word member))
  · apply Or.inr
    rw [((OriginalBinaryGenerator.machine families p operation).acceptedStreams_eq_empty_iff (generatorData n)).mpr
      (Set.not_nonempty_iff_eq_empty.mp active),measure_empty]

include expected in
def family (operation : OriginalBinarySelector.Operation) : UniformGenerators α where
  machine := OriginalBinaryGenerator.machine families p operation
  isGenerator := native_isGenerator families p expected operation

theorem family_layer (operation : OriginalBinarySelector.Operation) (n : ℕ) :
    (family families p expected operation).layer n=OriginalBinaryGenerator.layers families operation n :=
  OriginalBinaryGenerator.machine_language families p expected operation n

theorem family_expectedLength (mean : ∀ tag,(families tag).ExpectedLength)
    (operation : OriginalBinarySelector.Operation) : (family families p expected operation).ExpectedLength := by
  intro n active
  obtain ⟨word,member⟩ := active
  exact native_expectedLength families p expected mean operation n
    (native_available_of_member families p operation n word member)

theorem family_expectedTime (operation : OriginalBinarySelector.Operation) :
    (family families p expected operation).RawExpectedPolynomialTime := by
  refine ⟨expectedClock families p operation,?_⟩
  intro n active
  obtain ⟨word,member⟩ := active
  exact native_expectedRuntime families p expected operation n
    (native_available_of_member families p operation n word member)

theorem family_union_language : (family families p expected .union).language=
    (families false).language∪(families true).language :=
  UniformGenerators.language_eq_union_of_layers _ _ _ (family_layer families p expected .union)

theorem family_concat_language : (family families p expected .concatenation).language=
    IndexedSupport.concat (families false).language (families true).language :=
  UniformGenerators.language_eq_concat_of_layers _ _ _ (family_layer families p expected .concatenation)

theorem family_globalWordTime (fast : ∀ tag,(families tag).GlobalWordPolynomialTime)
    (operation : OriginalBinarySelector.Operation) : (family families p expected operation).GlobalWordPolynomialTime := by
  cases operation with
  | union =>
      obtain ⟨q,paths⟩ := OriginalBinaryGenerator.union_word_fast families p expected fast
      refine ⟨q,?_⟩
      intro word member
      rw [family_union_language] at member
      obtain ⟨n,bits,nonempty,run⟩ := paths word member
      refine ⟨n,bits,nonempty,?_⟩
      change (OriginalBinaryGenerator.machine families p .union).run (generatorData n) bits (q word.length)=.halted (.accepted word)
      exact run
  | concatenation =>
      obtain ⟨q,paths⟩ := OriginalBinaryGenerator.concat_word_fast families p expected fast
      refine ⟨q,?_⟩
      intro word member
      rw [family_concat_language] at member
      obtain ⟨n,bits,nonempty,run⟩ := paths word member
      refine ⟨n,bits,nonempty,?_⟩
      change (OriginalBinaryGenerator.machine families p .concatenation).run (generatorData n) bits (q word.length)=.halted (.accepted word)
      exact run

end ExpectedOriginalBinarySampling

namespace OriginalSourceClosure
omit [Fintype α] in
/-- Both sources can use one expected-time bound. -/
theorem common_expected_bound (G H : UniformGenerators α)
    (left : G.RawExpectedPolynomialTime) (right : H.RawExpectedPolynomialTime) :
    ∃ p : PolynomialBound,∀ (tag : Bool) j,((if tag then H else G).layer j).Nonempty →
      (if tag then H else G).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞) := by
  obtain ⟨p,left⟩ := left
  obtain ⟨q,right⟩ := right
  refine ⟨p.add q,?_⟩
  intro tag j active
  have bounds := p.add_le q j
  cases tag with
  | false => exact (left j active).trans (Nat.cast_le.mpr (by omega))
  | true => exact (right j active).trans (Nat.cast_le.mpr (by omega))
end OriginalSourceClosure

theorem elepg_union {L K : Language α} (left : L∈ELEPG α) (right : K∈ELEPG α) : L∪K∈ELEPG α := by
  obtain ⟨leftInfinite,G,leftLanguage,leftActive,leftMean,leftExpected,leftFast⟩ := left
  obtain ⟨_,H,rightLanguage,_,rightMean,rightExpected,rightFast⟩ := right
  obtain ⟨p,expected⟩ := OriginalSourceClosure.common_expected_bound G H leftExpected rightExpected
  let sources : Bool→UniformGenerators α := fun tag=>if tag then H else G
  have mean : ∀ tag,(sources tag).ExpectedLength := by intro tag; cases tag <;> assumption
  have fast : ∀ tag,(sources tag).GlobalWordPolynomialTime := by intro tag; cases tag <;> assumption
  let R := ExpectedOriginalBinarySampling.family sources p expected .union
  have layers : ∀ n,R.layer n=IndexedSupport.unionLayers G.layer H.layer n :=
    ExpectedOriginalBinarySampling.family_layer sources p expected .union
  have language : R.language=L∪K := by
    rw [ExpectedOriginalBinarySampling.family_union_language sources p expected]
    change G.language∪H.language=L∪K
    rw [leftLanguage,rightLanguage]
  exact mem_elepg_of_raw_expected_family (leftInfinite.mono Set.subset_union_left) R language
    (UniformGenerators.union_activeIndices_infinite R G H layers leftActive)
    (ExpectedOriginalBinarySampling.family_expectedLength sources p expected mean .union)
    (ExpectedOriginalBinarySampling.family_expectedTime sources p expected .union)
    (ExpectedOriginalBinarySampling.family_globalWordTime sources p expected fast .union)

theorem elepg_concatenation {L K : Language α} (left : L∈ELEPG α) (right : K∈ELEPG α) :
    IndexedSupport.concat L K∈ELEPG α := by
  obtain ⟨leftInfinite,G,leftLanguage,leftActive,leftMean,leftExpected,leftFast⟩ := left
  obtain ⟨rightInfinite,H,rightLanguage,rightActive,rightMean,rightExpected,rightFast⟩ := right
  obtain ⟨p,expected⟩ := OriginalSourceClosure.common_expected_bound G H leftExpected rightExpected
  let sources : Bool→UniformGenerators α := fun tag=>if tag then H else G
  have mean : ∀ tag,(sources tag).ExpectedLength := by intro tag; cases tag <;> assumption
  have fast : ∀ tag,(sources tag).GlobalWordPolynomialTime := by intro tag; cases tag <;> assumption
  let R := ExpectedOriginalBinarySampling.family sources p expected .concatenation
  have layers : ∀ n,R.layer n=IndexedSupport.concatLayers G.layer H.layer n :=
    ExpectedOriginalBinarySampling.family_layer sources p expected .concatenation
  have language : R.language=IndexedSupport.concat L K := by
    rw [ExpectedOriginalBinarySampling.family_concat_language sources p expected]
    change IndexedSupport.concat G.language H.language=IndexedSupport.concat L K
    rw [leftLanguage,rightLanguage]
  obtain ⟨j,rightLayer⟩ := rightActive.nonempty
  exact mem_elepg_of_raw_expected_family (IndexedSupport.concat_infinite_left leftInfinite rightInfinite.nonempty) R language
    (UniformGenerators.concat_activeIndices_infinite R G H layers leftActive j rightLayer)
    (ExpectedOriginalBinarySampling.family_expectedLength sources p expected mean .concatenation)
    (ExpectedOriginalBinarySampling.family_expectedTime sources p expected .concatenation)
    (ExpectedOriginalBinarySampling.family_globalWordTime sources p expected fast .concatenation)

end
end ComplexityOfGenerators
