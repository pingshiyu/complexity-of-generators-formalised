import ComplexityOfGenerators.Simulation.PairCollisionEncoderProperties
import ComplexityOfGenerators.Proofs.PairCollisionScaledMean
import ComplexityOfGenerators.Proofs.ELEPGCollision
import ComplexityOfGenerators.Proofs.ExpectedGenerationContainment
import ComplexityOfGenerators.Proofs.ExpectedLengthContainment

/-! Collision non-generability for the paper's literal `x#y` alphabet.
The native two-bit encoder preserves first moments up to the factor two.
The scaled-mean attack uses the original source index, so odd physical indices
and an unproved class-level encoding invariance play no role. -/
namespace ComplexityOfGenerators
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PairCollisionEncoding

def family (G : UniformGenerators PairSymbol) : UniformGenerators Bool where
  machine := PairCollisionEncoder.machine G.machine
  isGenerator n := PairCollisionEncoder.isGenerator G.machine (generatorData n) (G.isGenerator n)

theorem layer (G : UniformGenerators PairSymbol) (n : ℕ) :
    (family G).layer n=binaryPairWord '' G.layer n :=
  PairCollisionEncoder.generatedLanguage G.machine (generatorData n)

theorem mean (G : UniformGenerators PairSymbol) (expected : G.ExpectedLength)
    (n : ℕ) (active : n∈G.activeIndices) :
    (family G).machine.expectedLength (generatorData n)=(2*n : ℕ) := by
  change (PairCollisionEncoder.machine G.machine).expectedLength (generatorData n)=_
  rw [PairCollisionEncoder.expectedLength,expected n active]
  simp

theorem runtime (G : UniformGenerators PairSymbol) (p : PolynomialBound)
    (expected : ∀ n,n∈G.activeIndices → G.machine.expectedRuntime (generatorData n)≤(p n : ℝ≥0∞)) :
    ∃ q : PolynomialBound,∀ n,n∈G.activeIndices →
      (family G).machine.expectedRuntime (generatorData n)≤(q n : ℝ≥0∞) := by
  let q := (⟨2,0,by decide⟩ : PolynomialBound).mul p
  refine ⟨q,?_⟩
  intro n active
  have encoded := PairCollisionEncoder.expectedRuntime_le G.machine (generatorData n)
  have multiplied := mul_le_mul' (le_refl (2 : ℝ≥0∞)) (expected n active)
  apply encoded.trans (multiplied.trans_eq ?_)
  have value : q n=2*p n := by
    simp [q,PolynomialBound.mul,PolynomialBound.eval,Nat.mul_assoc]
  exact_mod_cast value.symm

theorem sound (h : HashFunction) (G : UniformGenerators PairSymbol)
    (source : ∀ n word,word∈G.layer n → word=[] ∨ word∈h.collisionLanguage) :
    ∀ n word,word∈(family G).layer n → word=[] ∨ word∈h.binaryCollisionLanguage := by
  intro n word member
  rw [layer] at member
  obtain ⟨original,member,rfl⟩ := member
  rcases source n original member with empty|collision
  · exact Or.inl (by simp [empty,binaryPairWord])
  · exact Or.inr ⟨original,collision,rfl⟩

end PairCollisionEncoding

theorem HashFunction.pair_collision_raw_impossible (h : HashFunction)
    (secure : h.CollisionResistant) (G : UniformGenerators PairSymbol)
    (active : G.activeIndices.Infinite) (mean : G.ExpectedLength)
    (expected : G.RawExpectedPolynomialTime)
    (sound : ∀ n word,word∈G.layer n → word=[] ∨ word∈h.collisionLanguage) : False := by
  obtain ⟨p,expected⟩ := expected
  obtain ⟨q,runtime⟩ := PairCollisionEncoding.runtime G p expected
  let encoded := PairCollisionEncoding.family G
  have soundEncoded := PairCollisionEncoding.sound h G sound
  apply h.scaled_expected_collision_generator_contradiction secure encoded G.activeIndices active q
    (fun n _ word member=>(soundEncoded n word member).symm)
    (PairCollisionEncoding.mean G mean) runtime
    (ExpectedCollisionSearch.finder encoded.machine (expectedCollisionClock q))
  exact fun n i index=>expectedCollisionFinder_stream_success h encoded (expectedCollisionClock q)
    soundEncoded n i index

theorem HashFunction.collisionLanguage_not_mem_expectedLengthExpectedPolynomialTime
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.collisionLanguage∉ExpectedLengthExpectedPolynomialTime PairSymbol := by
  rintro ⟨_,G,language,active,mean,expected⟩
  apply h.pair_collision_raw_impossible secure G active mean expected
  intro n word member
  exact Or.inr (language ▸ (show word∈G.language from ⟨n,member⟩))

theorem HashFunction.collisionLanguage_not_mem_elepg (h : HashFunction)
    (secure : h.CollisionResistant) : h.collisionLanguage∉ELEPG PairSymbol :=
  fun member=>h.collisionLanguage_not_mem_expectedLengthExpectedPolynomialTime secure
    (elepg_subset_expectedLengthExpectedPolynomialTime member)

theorem HashFunction.collisionLanguage_infinite (h : HashFunction) : h.collisionLanguage.Infinite := by
  apply Set.Infinite.of_image binaryPairWord
  have image : binaryPairWord '' h.collisionLanguage=h.binaryCollisionLanguage := by
    ext word
    simp [HashFunction.binaryCollisionLanguage,eq_comm]
  rw [image]
  exact h.binaryCollisionLanguage_infinite

theorem HashFunction.collisionLanguage_not_mem_epg (h : HashFunction)
    (secure : h.CollisionResistant) : h.collisionLanguage∉EPG PairSymbol := by
  intro member
  exact h.collisionLanguage_not_mem_elepg secure
    (epg_mem_elepg_of_infinite member h.collisionLanguage_infinite)

theorem HashFunction.collisionLanguage_not_mem_pg (h : HashFunction)
    (secure : h.CollisionResistant) : h.collisionLanguage∉PG PairSymbol :=
  fun member=>h.collisionLanguage_not_mem_epg secure (pg_subset_epg member)

end
end ComplexityOfGenerators
