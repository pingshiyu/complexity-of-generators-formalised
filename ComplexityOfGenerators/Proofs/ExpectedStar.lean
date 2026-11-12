import ComplexityOfGenerators.Proofs.ExpectedStarFamily
import ComplexityOfGenerators.Proofs.BoundedPhaseFamilies
import ComplexityOfGenerators.Foundations.ExpectedClosureBounds

/-! Native expected-time Kleene star for EPG and `LayerFastELEPG`.
These normalisation-based constructions use the historical per-layer fast-path
family requirements. Current ELEPG results are developed separately using
direct original-source calls. -/
namespace ComplexityOfGenerators
noncomputable section
variable {α : Type} [Fintype α]

namespace UniformGenerators

theorem language_eq_star_of_layers (R G : UniformGenerators α)
    (layers : ∀ n, R.layer n = IndexedSupport.starLayers G.layer n)
    (zero : ∀ word ∈ G.layer 0, word = []) :
    R.language = IndexedSupport.star G.language := by
  change IndexedSupport.language R.layer = IndexedSupport.star (IndexedSupport.language G.layer)
  rw [show R.layer = IndexedSupport.starLayers G.layer from funext layers,
    IndexedSupport.star_language G.layer zero]

theorem star_indexCoverage (R G : UniformGenerators α)
    (layers : ∀ n, R.layer n = IndexedSupport.starLayers G.layer n)
    (coverage : G.PolynomialIndexCoverage) (zero : ∀ word ∈ G.layer 0, word = []) :
    R.PolynomialIndexCoverage := by
  obtain ⟨q,covered⟩ := coverage
  refine ⟨IndexedSupport.starBound q,?_⟩
  intro word member
  rw [language_eq_star_of_layers R G layers zero] at member
  obtain ⟨n,small,generated⟩ := IndexedSupport.star_coverage G.layer q covered zero word member
  exact ⟨n,small,by rwa [layers]⟩

end UniformGenerators

theorem epg_star {L : Language α} (member : L ∈ EPG α) : IndexedSupport.star L ∈ EPG α := by
  obtain ⟨G,language,p,expected,short⟩ := member
  let P := BoundedPhaseFamily.ofExpected G.toUniformGenerators G.expectedLength ⟨p,expected,short⟩
  have phaseLayers : ∀ n, P.layer n = G.toUniformGenerators.layer n :=
    BoundedPhaseFamily.ofExpected_layer G.toUniformGenerators G.expectedLength ⟨p,expected,short⟩
  let R := ExpectedStarSampling.family G.toUniformGenerators p expected P phaseLayers
  have layers : ∀ n, R.layer n = IndexedSupport.starLayers G.toUniformGenerators.layer n :=
    ExpectedStarSampling.family_layer G.toUniformGenerators p expected P phaseLayers
  have zero : ∀ word ∈ G.toUniformGenerators.layer 0, word = [] := by
    intro word generated
    exact List.length_eq_zero_iff.mp (G.outputLength 0 word generated)
  let exactFamily : GeneratorFamily α := {
    machine := R.machine
    isGenerator := R.isGenerator
    outputLength := by
      intro n word generated
      rw [layers] at generated
      exact IndexedSupport.starLayers_length G.toUniformGenerators.layer G.outputLength n word generated }
  refine ⟨exactFamily,?_,ExpectedStarSampling.family_expectedPolynomialTime
    G.toUniformGenerators p expected P phaseLayers⟩
  change R.language = IndexedSupport.star L
  rw [UniformGenerators.language_eq_star_of_layers R G.toUniformGenerators layers zero,language]

theorem layerFastELEPG_star {L : Language α} (member : L ∈ LayerFastELEPG α) : IndexedSupport.star L ∈ LayerFastELEPG α := by
  obtain ⟨infinite,G,language,_,mean,⟨p,expected,short⟩,coverage⟩ := member
  let P := BoundedPhaseFamily.ofExpected G mean ⟨p,expected,short⟩
  have phaseLayers : ∀ n, P.layer n = G.layer n :=
    BoundedPhaseFamily.ofExpected_layer G mean ⟨p,expected,short⟩
  let R := ExpectedStarSampling.family G p expected P phaseLayers
  have layers : ∀ n, R.layer n = IndexedSupport.starLayers G.layer n :=
    ExpectedStarSampling.family_layer G p expected P phaseLayers
  have zero : ∀ word ∈ G.layer 0, word = [] :=
    fun _ generated => G.word_eq_nil_of_expectedLength_zero mean generated
  have outputLanguage : R.language = IndexedSupport.star L := by
    rw [UniformGenerators.language_eq_star_of_layers R G layers zero,language]
  exact mem_layerFastELEPG_of_expected_family (IndexedSupport.star_infinite infinite) R outputLanguage
    (ExpectedStarSampling.family_expectedLength G p expected P phaseLayers)
    (ExpectedStarSampling.family_expectedPolynomialTime G p expected P phaseLayers)
    (UniformGenerators.star_indexCoverage R G layers coverage zero)

end
end ComplexityOfGenerators
