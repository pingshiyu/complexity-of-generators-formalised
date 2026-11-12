import ComplexityOfGenerators.Proofs.ExpectedCollisionReduction
import ComplexityOfGenerators.Foundations.StreamSemanticsProperties

/-! The binary attacker also contradicts families whose mean length at index
`i` is `2*i`. This is the mean produced by encoding the paper's collision
alphabet with fixed two-bit blocks; no family-index conversion is required. -/
namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal
noncomputable section

private theorem pair_encoded_atom_parameter (h : HashFunction) (G : UniformGenerators Bool)
    (i m : ℕ) (positive : 0<m)
    (sound : ∀ word∈G.layer i,word∈h.binaryCollisionLanguage ∨ word=[])
    (mass : 0<fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream=m}) :
    ∃ n,m=expectedCollisionLength n := by
  have nonempty : {stream | G.machine.streamLength (generatorData i) stream=m}.Nonempty := by
    by_contra absent
    rw [Set.not_nonempty_iff_eq_empty.mp absent,measure_empty] at mass
    exact (lt_irrefl _ mass)
  obtain ⟨stream,length⟩ := nonempty
  obtain ⟨word,member,produces,wordLength⟩ := G.machine.streamLength_pos_mem_generatedLanguage
    (generatorData i) (length.symm ▸ positive)
  have size : word.length=m := wordLength.trans length
  rcases sound word member with collision|empty
  · obtain ⟨pair,⟨n,x,y,collision,rfl⟩,rfl⟩ := collision
    obtain ⟨a,b,rfl,rfl,different,same⟩ := collision
    refine ⟨n,?_⟩
    simp only [binaryPairWord_length,encodePair_length,bitsWord_length] at size
    unfold expectedCollisionLength
    omega
  · simp only [empty,List.length_nil] at size
    omega

theorem HashFunction.infinitely_many_scaled_expected_collision_atoms
    (h : HashFunction) (G : UniformGenerators Bool) (indices : Set ℕ)
    (infinite : indices.Infinite)
    (sound : ∀ i∈indices,∀ word∈G.layer i,word∈h.binaryCollisionLanguage ∨ word=[])
    (mean : ∀ i∈indices,G.machine.expectedLength (generatorData i)=(2*i : ℕ)) :
    Set.Infinite {n : ℕ | ∃ i∈indices,i≤2*expectedCollisionLength n ∧
      ((((expectedCollisionLength n : ℝ≥0∞)+1)^3)⁻¹)≤
        fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream=expectedCollisionLength n}} := by
  apply Set.infinite_of_forall_exists_gt
  intro bound
  obtain ⟨i,active,largeIndex⟩ := infinite.exists_gt (max 5 (2*expectedCollisionLength (bound+1)))
  have hi : 5≤2*i := by omega
  obtain ⟨m,index,atom⟩ := exists_heavy_length_atom fairCoinMeasure
    (G.machine.streamLength (generatorData i))
    (G.machine.measurable_streamLength (generatorData i)) (2*i) hi (mean i active)
  have positive : 0<m := by omega
  have atomPositive : 0<fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream=m} := by
    have nonzero : (((m : ℝ≥0∞)+1)^3)⁻¹≠0 := by
      apply ENNReal.inv_ne_zero.mpr
      exact ENNReal.pow_ne_top (by simp)
    exact (bot_lt_iff_ne_bot.mpr nonzero).trans_le atom
  obtain ⟨n,size⟩ := pair_encoded_atom_parameter h G i m positive (sound i active) atomPositive
  refine ⟨n,⟨i,active,?_,?_⟩,?_⟩
  · rw [size] at index
    omega
  · simpa only [size] using atom
  · rw [size] at index
    unfold expectedCollisionLength at largeIndex index
    omega

theorem HashFunction.scaled_expected_collision_generator_contradiction
    (h : HashFunction) (secure : h.CollisionResistant)
    (G : UniformGenerators Bool) (indices : Set ℕ) (infinite : indices.Infinite)
    (p : PolynomialBound)
    (sound : ∀ i∈indices,∀ word∈G.layer i,word∈h.binaryCollisionLanguage ∨ word=[])
    (mean : ∀ i∈indices,G.machine.expectedLength (generatorData i)=(2*i : ℕ))
    (runtime : ∀ i∈indices,G.machine.expectedRuntime (generatorData i)≤(p i : ℝ≥0∞))
    (A : CollisionFinder)
    (simulation : ∀ n i,i≤2*expectedCollisionLength n →
      {stream | G.machine.streamLength (generatorData i) stream=expectedCollisionLength n ∧
        G.machine.streamRuntime (generatorData i) stream≤(expectedCollisionClock p n : ℝ≥0∞)}⊆
          collisionSuccess h A n) : False := by
  apply secure
  refine ⟨A,expectedCollisionDenominator,?_⟩
  apply (h.infinitely_many_scaled_expected_collision_atoms G indices infinite sound mean).mono
  rintro n ⟨i,active,index,atom⟩
  have joint := measure_joint_runtime_ge_half fairCoinMeasure
    {stream | G.machine.streamLength (generatorData i) stream=expectedCollisionLength n}
    (G.machine.streamRuntime (generatorData i))
    (G.machine.measurable_streamRuntime (generatorData i)).aemeasurable
    (p i : ℝ≥0∞) (expectedCollisionClock p n : ℝ≥0∞)
    ((((expectedCollisionLength n : ℝ≥0∞)+1)^3)⁻¹)
    (runtime i active) (by exact_mod_cast (expectedCollisionClock_positive p n).ne')
    (ENNReal.natCast_ne_top _) atom (by simp) (expectedCollisionClock_loss p n i index)
  have contained : fairCoinMeasure {stream |
      G.machine.streamLength (generatorData i) stream=expectedCollisionLength n ∧
      G.machine.streamRuntime (generatorData i) stream≤(expectedCollisionClock p n : ℝ≥0∞)}≤
        fairCoinMeasure (collisionSuccess h A n) := measure_mono (simulation n i index)
  exact (expectedCollisionDenominator_strict n).trans_le (joint.trans contained)

end
end ComplexityOfGenerators
