import ComplexityOfGenerators.Foundations.ExpectedLengthBounds
import ComplexityOfGenerators.Foundations.StreamPrefixExecution
import ComplexityOfGenerators.Foundations.BinaryCollisions

/-!
# First-moment reduction from expected-length collision generators

The algebraic reduction is separate from the native finite-machine compiler.
The simulation obligation is explicit and is discharged by the actual bounded
index-search construction. Neither a variance bound nor an independent runtime
distribution is assumed. The source may additionally produce the empty word;
this stronger form is used for the intersection nonclosure witness.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

/-- Length of the binary encoding of a collision at parameter `n`. -/
def expectedCollisionLength (n : ℕ) : ℕ := 4 * (n + 1) + 2

private noncomputable def collisionLengthPolynomial : Polynomial ℕ :=
  4 * (Polynomial.X + 1) + 2

private theorem collisionLengthPolynomial_eval (n : ℕ) :
    collisionLengthPolynomial.eval n = expectedCollisionLength n := by
  simp [collisionLengthPolynomial, expectedCollisionLength]

/-- A polynomial clock large enough to retain half the heavy atom's mass. -/
noncomputable def expectedCollisionClock (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (2 * (collisionLengthPolynomial + 1) ^ 3 *
      p.asPolynomial.comp (2 * collisionLengthPolynomial))

theorem expectedCollisionClock_bound (p : PolynomialBound) (n : ℕ) :
    2 * (expectedCollisionLength n + 1) ^ 3 * p (2 * expectedCollisionLength n) ≤
      expectedCollisionClock p n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (2 * (collisionLengthPolynomial + 1) ^ 3 *
      p.asPolynomial.comp (2 * collisionLengthPolynomial)) n
  simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, Polynomial.eval_comp,
    PolynomialBound.asPolynomial_eval, collisionLengthPolynomial_eval,
    expectedCollisionClock] using bound

theorem expectedCollisionClock_positive (p : PolynomialBound) (n : ℕ) :
    0 < expectedCollisionClock p n := (expectedCollisionClock p).positive n

/-- A strict inverse-polynomial threshold below the surviving heavy mass. -/
noncomputable def expectedCollisionDenominator : PolynomialBound :=
  PolynomialBound.ofPolynomial (4 * (collisionLengthPolynomial + 1) ^ 3)

theorem expectedCollisionDenominator_bound (n : ℕ) :
    4 * (expectedCollisionLength n + 1) ^ 3 ≤ expectedCollisionDenominator n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (4 * (collisionLengthPolynomial + 1) ^ 3) n
  simpa only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, Polynomial.eval_one, collisionLengthPolynomial_eval,
    expectedCollisionDenominator] using bound

private theorem polynomialBound_mono (p : PolynomialBound) {a b : ℕ} (bound : a ≤ b) :
    p a ≤ p b := by
  change p.coefficient * (a + 1) ^ p.degree ≤ p.coefficient * (b + 1) ^ p.degree
  exact Nat.mul_le_mul_left _ (pow_le_pow_left' (by omega) _)

private theorem heavy_half_eq_inv (m : ℕ) :
    ((((m : ℝ≥0∞) + 1) ^ 3)⁻¹) / 2 =
      (((2 * (m + 1) ^ 3 : ℕ) : ℝ≥0∞)⁻¹) := by
  simp only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one,
    div_eq_mul_inv]
  rw [ENNReal.mul_inv (Or.inl (by norm_num)) (Or.inl (by norm_num)), mul_comm]

theorem expectedCollisionClock_loss (p : PolynomialBound) (n i : ℕ)
    (index : i ≤ 2 * expectedCollisionLength n) :
    (p i : ℝ≥0∞) / (expectedCollisionClock p n : ℝ≥0∞) ≤
      ((((expectedCollisionLength n : ℝ≥0∞) + 1) ^ 3)⁻¹) / 2 := by
  rw [heavy_half_eq_inv]
  have natural : p i * (2 * (expectedCollisionLength n + 1) ^ 3) ≤
      expectedCollisionClock p n := by
    calc
      p i * (2 * (expectedCollisionLength n + 1) ^ 3) ≤
          p (2 * expectedCollisionLength n) * (2 * (expectedCollisionLength n + 1) ^ 3) :=
        Nat.mul_le_mul_right _ (polynomialBound_mono p index)
      _ = 2 * (expectedCollisionLength n + 1) ^ 3 * p (2 * expectedCollisionLength n) :=
        Nat.mul_comm _ _
      _ ≤ _ := expectedCollisionClock_bound p n
  have cast : (p i : ℝ≥0∞) * ((2 * (expectedCollisionLength n + 1) ^ 3 : ℕ) : ℝ≥0∞) ≤
      (expectedCollisionClock p n : ℝ≥0∞) := by exact_mod_cast natural
  have denominator_pos : ((2 * (expectedCollisionLength n + 1) ^ 3 : ℕ) : ℝ≥0∞) ≠ 0 := by
    positivity
  have denominator_finite : ((2 * (expectedCollisionLength n + 1) ^ 3 : ℕ) : ℝ≥0∞) ≠ ⊤ := by
    exact ENNReal.natCast_ne_top _
  apply (ENNReal.div_le_iff (by exact_mod_cast (expectedCollisionClock_positive p n).ne') (by simp)).2
  rw [mul_comm]
  have scaled : (p i : ℝ≥0∞) *
      ((2 * (expectedCollisionLength n + 1) ^ 3 : ℕ) : ℝ≥0∞) *
      (((2 * (expectedCollisionLength n + 1) ^ 3 : ℕ) : ℝ≥0∞)⁻¹) ≤
      (expectedCollisionClock p n : ℝ≥0∞) *
      (((2 * (expectedCollisionLength n + 1) ^ 3 : ℕ) : ℝ≥0∞)⁻¹) := by
    gcongr
  simpa only [ENNReal.mul_inv_cancel_right denominator_pos denominator_finite] using scaled

theorem expectedCollisionDenominator_strict (n : ℕ) :
    (expectedCollisionDenominator n : ℝ≥0∞)⁻¹ <
      ((((expectedCollisionLength n : ℝ≥0∞) + 1) ^ 3)⁻¹) / 2 := by
  rw [heavy_half_eq_inv, ENNReal.inv_lt_inv]
  have positive : 0 < (expectedCollisionLength n + 1) ^ 3 := by positivity
  have bound := expectedCollisionDenominator_bound n
  exact_mod_cast (show 2 * (expectedCollisionLength n + 1) ^ 3 <
      expectedCollisionDenominator n by omega)

private theorem streamProduces_mem_layer (G : UniformGenerators Bool) (i : ℕ)
    {stream : BitStream} {word : BitString}
    (produced : G.machine.streamProduces (generatorData i) stream word) : word ∈ G.layer i := by
  obtain ⟨bits, member, produces⟩ := produced
  exact ⟨bits ++ [false], by simp, G.machine.produces_append (generatorData i) bits [false] word produces⟩

private theorem collision_atom_has_parameter (h : HashFunction) (G : UniformGenerators Bool)
    (firstIndex i m : ℕ) (first : firstIndex ≤ i) (positive : 0 < m)
    (sound : ∀ j, firstIndex ≤ j → ∀ word ∈ G.layer j,
      word ∈ h.binaryCollisionLanguage ∨ word = [])
    (mass : 0 < fairCoinMeasure {stream |
      G.machine.streamLength (generatorData i) stream = m}) :
    ∃ n, m = expectedCollisionLength n := by
  have nonempty : {stream | G.machine.streamLength (generatorData i) stream = m}.Nonempty := by
    by_contra absent
    rw [Set.not_nonempty_iff_eq_empty.mp absent, measure_empty] at mass
    exact (lt_irrefl _ mass)
  obtain ⟨stream, length⟩ := nonempty
  rcases G.machine.streamLength_spec (generatorData i) stream with produced | ⟨zero, absent⟩
  · obtain ⟨word, output, wordLength⟩ := produced
    have size : word.length = m := wordLength.trans length
    rcases sound i first word (streamProduces_mem_layer G i output) with collision | empty
    · obtain ⟨pair, ⟨n, x, y, collision, rfl⟩, rfl⟩ := collision
      obtain ⟨a, b, rfl, rfl, different, same⟩ := collision
      refine ⟨n, ?_⟩
      simp only [binaryPairWord_length, encodePair_length, bitsWord_length] at size
      unfold expectedCollisionLength
      omega
    · simp only [empty, List.length_nil] at size
      omega
  · change G.machine.streamLength (generatorData i) stream = m at length
    omega

/-- Expected-size families supported on collisions (possibly also the empty
word) have inverse-cubic atoms at infinitely many collision parameters. -/
theorem HashFunction.infinitely_many_expected_collision_atoms (h : HashFunction)
    (G : UniformGenerators Bool) (firstIndex : ℕ)
    (sound : ∀ i, firstIndex ≤ i → ∀ word ∈ G.layer i,
      word ∈ h.binaryCollisionLanguage ∨ word = [])
    (mean : ∀ i, firstIndex ≤ i →
      G.machine.expectedLength (generatorData i) = (i : ℝ≥0∞)) :
    Set.Infinite {n : ℕ | ∃ i : ℕ, firstIndex ≤ i ∧ i ≤ 2 * expectedCollisionLength n ∧
      ((((expectedCollisionLength n : ℝ≥0∞) + 1) ^ 3)⁻¹) ≤
        fairCoinMeasure {stream |
          G.machine.streamLength (generatorData i) stream = expectedCollisionLength n}} := by
  let mass : ℕ → ℕ → ℝ≥0∞ := fun i m =>
    fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream = m}
  have total : ∀ i, firstIndex ≤ i → (∑' m : ℕ, mass i m) ≤ 1 := by
    intro i hi
    exact (tsum_nat_atom_measures_eq_one fairCoinMeasure
      (G.machine.streamLength (generatorData i)) (G.machine.measurable_streamLength _)).le
  have moment : ∀ i, firstIndex ≤ i →
      (∑' m : ℕ, (m : ℝ≥0∞) * mass i m) = (i : ℝ≥0∞) := by
    intro i hi
    rw [← lintegral_nat_eq_tsum_atoms fairCoinMeasure
      (G.machine.streamLength (generatorData i)) (G.machine.measurable_streamLength _)]
    exact mean i hi
  apply Set.infinite_of_forall_exists_gt
  intro bound
  obtain ⟨i, m, first, large, index, atom⟩ :=
    unbounded_heavy_length_atoms_of_mass mass firstIndex total moment
      (expectedCollisionLength (bound + 1))
  have positive : 0 < m := by unfold expectedCollisionLength at large; omega
  have atom_pos : 0 < mass i m := by
    have nonzero : (((m : ℝ≥0∞) + 1) ^ 3)⁻¹ ≠ 0 := by
      apply ENNReal.inv_ne_zero.mpr
      exact ENNReal.pow_ne_top (by simp)
    exact (bot_lt_iff_ne_bot.mpr nonzero).trans_le atom
  obtain ⟨n, size⟩ := collision_atom_has_parameter h G firstIndex i m first positive sound atom_pos
  refine ⟨n, ⟨i, first, ?_, ?_⟩, ?_⟩
  · simpa only [size] using index
  · simpa only [size] using atom
  · rw [size] at large
    unfold expectedCollisionLength at large
    omega

/-- A native collision finder with the stated bounded-search simulation property
contradicts collision resistance. The surrounding compiler supplies this property;
it is neither assumed globally nor hidden as an axiom. -/
theorem HashFunction.expected_collision_generator_contradiction (h : HashFunction)
    (secure : h.CollisionResistant) (G : UniformGenerators Bool) (firstIndex : ℕ)
    (p : PolynomialBound)
    (sound : ∀ i, firstIndex ≤ i → ∀ word ∈ G.layer i,
      word ∈ h.binaryCollisionLanguage ∨ word = [])
    (mean : ∀ i, firstIndex ≤ i →
      G.machine.expectedLength (generatorData i) = (i : ℝ≥0∞))
    (runtime : ∀ i, firstIndex ≤ i →
      G.machine.expectedRuntime (generatorData i) ≤ (p i : ℝ≥0∞))
    (A : CollisionFinder)
    (simulation : ∀ n i, i ≤ 2 * expectedCollisionLength n →
      {stream | G.machine.streamLength (generatorData i) stream = expectedCollisionLength n ∧
        G.machine.streamRuntime (generatorData i) stream ≤ (expectedCollisionClock p n : ℝ≥0∞)} ⊆
          collisionSuccess h A n) : False := by
  apply secure
  refine ⟨A, expectedCollisionDenominator, ?_⟩
  apply (h.infinitely_many_expected_collision_atoms G firstIndex sound mean).mono
  rintro n ⟨i, first, index, atom⟩
  have joint := measure_joint_runtime_ge_half fairCoinMeasure
    {stream | G.machine.streamLength (generatorData i) stream = expectedCollisionLength n}
    (G.machine.streamRuntime (generatorData i))
    (G.machine.measurable_streamRuntime (generatorData i)).aemeasurable
    (p i : ℝ≥0∞) (expectedCollisionClock p n : ℝ≥0∞)
    ((((expectedCollisionLength n : ℝ≥0∞) + 1) ^ 3)⁻¹)
    (runtime i first)
    (by exact_mod_cast (expectedCollisionClock_positive p n).ne')
    (ENNReal.natCast_ne_top _)
    atom
    (by simp)
    (expectedCollisionClock_loss p n i index)
  have contained : fairCoinMeasure {stream |
      G.machine.streamLength (generatorData i) stream = expectedCollisionLength n ∧
      G.machine.streamRuntime (generatorData i) stream ≤ (expectedCollisionClock p n : ℝ≥0∞)} ≤
        fairCoinMeasure (collisionSuccess h A n) := measure_mono (simulation n i index)
  exact (expectedCollisionDenominator_strict n).trans_le (joint.trans contained)

end ComplexityOfGenerators
