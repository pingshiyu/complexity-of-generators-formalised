import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Total
import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Support
import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Witness
import ComplexityOfGenerators.Proofs.OriginalStarNativeProperties
import ComplexityOfGenerators.Proofs.OriginalStarFastRecords
import ComplexityOfGenerators.Proofs.OriginalSourceFamilyCriteria

/-! Kleene-star closure for the current paper's ELEPG. The native construction
uses original source calls and global word-length fast paths throughout. -/
namespace ComplexityOfGenerators
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Simulation MeasureTheory
open scoped ENNReal
variable {α : Type} [Fintype α]

namespace ExpectedOriginalStarSampling
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

theorem native_available_of_member (n : ℕ) (word : List α)
    (member : word∈(OriginalStarGenerator.machine G.machine p).generatedLanguage (generatorData n)) :
    ExpectedStarSampling.Available G n := by
  obtain ⟨parts,total,active⟩ := IndexedSupport.starLayers_available G.layer n word
    (OriginalStarGenerator.machine_language_subset G p n member)
  exact ⟨parts,total,active⟩

include expected in
theorem native_isGenerator (n : ℕ) : (OriginalStarGenerator.machine G.machine p).IsGenerator (generatorData n) := by
  refine ⟨OriginalStarGenerator.machine_halting G p n,?_⟩
  by_cases active : ((OriginalStarGenerator.machine G.machine p).generatedLanguage (generatorData n)).Nonempty
  · obtain ⟨word,member⟩ := active
    exact Or.inl (native_productive G p expected n (native_available_of_member G p n word member))
  · apply Or.inr
    rw [((OriginalStarGenerator.machine G.machine p).acceptedStreams_eq_empty_iff (generatorData n)).mpr
      (Set.not_nonempty_iff_eq_empty.mp active),measure_empty]

include expected in
def family : UniformGenerators α where
  machine := OriginalStarGenerator.machine G.machine p
  isGenerator := native_isGenerator G p expected

theorem family_layer (n : ℕ) : (family G p expected).layer n=IndexedSupport.starLayers G.layer n :=
  Set.Subset.antisymm (OriginalStarGenerator.machine_language_subset G p n)
    (OriginalStarGenerator.machine_language_superset G p expected n)

theorem family_expectedLength (mean : G.ExpectedLength) : (family G p expected).ExpectedLength := by
  intro n active
  obtain ⟨word,member⟩ := active
  exact native_expectedLength G p expected mean n (native_available_of_member G p n word member)

theorem family_expectedTime : (family G p expected).RawExpectedPolynomialTime := by
  refine ⟨expectedClock G p,?_⟩
  intro n active
  obtain ⟨word,member⟩ := active
  exact native_expectedRuntime G p expected n (native_available_of_member G p n word member)

theorem family_language (mean : G.ExpectedLength) : (family G p expected).language=IndexedSupport.star G.language := by
  change IndexedSupport.language (family G p expected).layer=IndexedSupport.star (IndexedSupport.language G.layer)
  rw [show (family G p expected).layer=IndexedSupport.starLayers G.layer from funext (family_layer G p expected)]
  exact IndexedSupport.star_language G.layer (fun _ member=>G.word_eq_nil_of_expectedLength_zero mean member)

theorem family_globalWordTime (mean : G.ExpectedLength) (fast : G.GlobalWordPolynomialTime) :
    (family G p expected).GlobalWordPolynomialTime := by
  obtain ⟨q,recordsFor⟩ := OriginalSourceClosure.star_fast_records G mean fast
  apply OriginalSourceClosure.globalWordPolynomialTime_of_call_paths (family G p expected)
    (outerClock G p) callClock (IndexedSupport.starBound q) (OriginalSourceClosure.wordWork q)
  intro word member
  rw [family_language G p expected mean] at member
  obtain ⟨n,parts,records,index,available,labels,minimal,output,timeBound⟩ := recordsFor word member
  obtain ⟨bits,ticks,nonempty,bound,run⟩ := OriginalStarGenerator.runs_records G p expected n parts records
    available labels minimal
  refine ⟨n,bits,ticks,nonempty,index,?_,?_⟩
  · apply bound.trans
    rw [←outerClock_eval]
    exact Nat.add_le_add_left (Nat.mul_le_mul (callClock_lower n) timeBound) _
  · change (OriginalStarGenerator.machine G.machine p).run (generatorData n) bits ticks=.halted (.accepted word)
    simpa only [output] using run

end ExpectedOriginalStarSampling

theorem elepg_star {L : Language α} (member : L∈ELEPG α) : IndexedSupport.star L∈ELEPG α := by
  obtain ⟨infinite,G,language,active,mean,⟨p,expected⟩,fast⟩ := member
  let R := ExpectedOriginalStarSampling.family G p expected
  have layers : ∀ n,R.layer n=IndexedSupport.starLayers G.layer n := ExpectedOriginalStarSampling.family_layer G p expected
  have outputLanguage : R.language=IndexedSupport.star L := by
    rw [ExpectedOriginalStarSampling.family_language G p expected mean,language]
  exact mem_elepg_of_raw_expected_family (IndexedSupport.star_infinite infinite) R outputLanguage
    (UniformGenerators.star_activeIndices_infinite R G layers active)
    (ExpectedOriginalStarSampling.family_expectedLength G p expected mean)
    (ExpectedOriginalStarSampling.family_expectedTime G p expected)
    (ExpectedOriginalStarSampling.family_globalWordTime G p expected mean fast)

end
end ComplexityOfGenerators
