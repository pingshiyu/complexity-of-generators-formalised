import ComplexityOfGenerators.Proofs.ExactRecursiveTables
import ComplexityOfGenerators.Proofs.ExactRecursiveSampling

/-! Base sampling and the corrected walk with a polynomial complete label table. -/

namespace ComplexityOfGenerators.ExactRecursiveGenerators

variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : ExactRecursiveGenerators R)
variable (seed time : PolynomialBound) (bounded : G.base.RunsInTime seed time)

def tableAlgorithmSeed (E : LabelEnumeration R) (n : ℕ) : ℕ :=
  seed n + G.tableWalkSeed E n (R.rankBound n)

def tableAlgorithm (E : LabelEnumeration R) (n : ℕ) (bits : BitString) : Option (Word α) :=
  (G.baseTrial time n (bits.take (seed n))).bind fun y =>
    G.tableWalk E n (R.rankBound n) y (bits.drop (seed n))

theorem tableAlgorithm_split_lengths (E : LabelEnumeration R) (n : ℕ) {bits : BitString}
    (length : bits.length = G.tableAlgorithmSeed seed E n) :
    (bits.take (seed n)).length = seed n ∧
      (bits.drop (seed n)).length = G.tableWalkSeed E n (R.rankBound n) := by
  simp only [tableAlgorithmSeed] at length
  simp only [List.length_take, List.length_drop]
  constructor <;> omega

include bounded in
theorem tableAlgorithm_sound {E : LabelEnumeration R} {n : ℕ} {bits : BitString} {x : Word α}
    (length : bits.length = G.tableAlgorithmSeed seed E n)
    (output : G.tableAlgorithm seed time E n bits = some x) : x ∈ lengthSlice L n := by
  obtain ⟨baseLength, walkLength⟩ := G.tableAlgorithm_split_lengths seed E n length
  unfold tableAlgorithm at output
  cases base : G.baseTrial time n (bits.take (seed n)) with
  | none => simp [base] at output
  | some y =>
    have member := G.baseTrial_sound seed time bounded baseLength base
    exact R.walk_sound member.1 (G.tableWalk_sound member.1 walkLength (by simpa [base] using output))

include bounded in
theorem tableAlgorithm_complete (E : LabelEnumeration R) 
    {n : ℕ} {x : Word α} (member : x ∈ lengthSlice L n) :
    ∃ bits, bits.length = G.tableAlgorithmSeed seed E n ∧
      G.tableAlgorithm seed time E n bits = some x := by
  obtain ⟨y, baseMember, path⟩ := R.slice_has_base member
  have target := R.walk_covers_path member baseMember.1.1 path (R.rankBound n)
    (by have := R.ancestor_rank_le (R.slice_subset_ancestors n member); omega)
  obtain ⟨front, frontLength, base⟩ := G.baseTrial_complete seed time bounded baseMember
  obtain ⟨rest, restLength, walk⟩ := G.tableWalk_complete E baseMember.1 target
  refine ⟨front ++ rest, ?_, ?_⟩
  · simp [tableAlgorithmSeed, frontLength, restLength]
  · simpa [tableAlgorithm, ← frontLength, base] using walk

include bounded in
theorem tableAlgorithm_total (E : LabelEnumeration R) 
    {n : ℕ} (nonempty : (lengthSlice L n).Nonempty) {bits : BitString}
    (length : bits.length = G.tableAlgorithmSeed seed E n) :
    ∃ x, G.tableAlgorithm seed time E n bits = some x := by
  obtain ⟨baseLength, walkLength⟩ := G.tableAlgorithm_split_lengths seed E n length
  obtain ⟨y, base⟩ := G.baseTrial_total seed time bounded nonempty baseLength
  have member := G.baseTrial_sound seed time bounded baseLength base
  obtain ⟨x, walk⟩ := G.tableWalk_total E member.1 (by omega) walkLength
  exact ⟨x, by simpa [tableAlgorithm, base] using walk⟩

include bounded in
/-- Exact support of the assembled, executable finite-seed tableAlgorithm. -/
theorem tableAlgorithm_support (E : LabelEnumeration R)  (n : ℕ) :
    {x | ∃ bits, bits.length = G.tableAlgorithmSeed seed E n ∧
      G.tableAlgorithm seed time E n bits = some x} = lengthSlice L n := by
  ext x
  exact ⟨fun ⟨_, length, output⟩ => G.tableAlgorithm_sound seed time bounded length output,
    G.tableAlgorithm_complete seed time bounded E⟩

include bounded in
/-- Every full seed succeeds exactly when the target length slice is nonempty. -/
theorem tableAlgorithm_full_trial_iff (E : LabelEnumeration R) 
    (n : ℕ) (bits : BitString) (length : bits.length = G.tableAlgorithmSeed seed E n) :
    (∃ x, G.tableAlgorithm seed time E n bits = some x) ↔ (lengthSlice L n).Nonempty :=
  ⟨fun ⟨x, output⟩ => ⟨x, G.tableAlgorithm_sound seed time bounded length output⟩,
    fun nonempty => G.tableAlgorithm_total seed time bounded E nonempty length⟩

/-- Polynomial bound including both the source trial seeds and all selection
and stopping coins. This is a seed bound, not a native running-time claim. -/
noncomputable def tableAlgorithmSeedBound (E : LabelEnumeration R) : PolynomialBound :=
  PolynomialBound.ofPolynomial (seed.asPolynomial + R.rankBound.asPolynomial *
    (1 + (E.bound).asPolynomial * (G.inverseSeed.asPolynomial + 1)))

theorem tableAlgorithm_seed_polynomial (E : LabelEnumeration R) (n : ℕ) :
    G.tableAlgorithmSeed seed E n ≤ G.tableAlgorithmSeedBound seed E n := by
  have count := E.length_le n
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    PolynomialBound.asPolynomial_eval, tableAlgorithmSeed, tableWalkSeed, tableSeed]
  gcongr

theorem tableAlgorithm_append (E : LabelEnumeration R) (n : ℕ) {bits : BitString}
    (length : bits.length = G.tableAlgorithmSeed seed E n) (extra : BitString) :
    G.tableAlgorithm seed time E n (bits ++ extra) = G.tableAlgorithm seed time E n bits := by
  obtain ⟨baseLength, walkLength⟩ := G.tableAlgorithm_split_lengths seed E n length
  have enough : seed n ≤ bits.length := by simp only [tableAlgorithmSeed] at length; omega
  simp only [tableAlgorithm, List.take_append_of_le_length enough, List.drop_append_of_le_length enough]
  cases G.baseTrial time n (bits.take (seed n)) with
  | none => rfl
  | some y => exact G.tableWalk_append E n (R.rankBound n) y walkLength extra

theorem tableAlgorithm_take (E : LabelEnumeration R) (n : ℕ) {bits : BitString}
    (enough : G.tableAlgorithmSeed seed E n ≤ bits.length) :
    G.tableAlgorithm seed time E n bits =
      G.tableAlgorithm seed time E n (bits.take (G.tableAlgorithmSeed seed E n)) := by
  have length : (bits.take (G.tableAlgorithmSeed seed E n)).length = G.tableAlgorithmSeed seed E n :=
    by simp [Nat.min_eq_left enough]
  simpa using G.tableAlgorithm_append seed time E n length (bits.drop (G.tableAlgorithmSeed seed E n))

include bounded in
/-- Padding to the polynomial budget preserves exact support. -/
theorem polynomial_tableAlgorithm_support (E : LabelEnumeration R)  (n : ℕ) :
    {x | ∃ bits, bits.length = G.tableAlgorithmSeedBound seed E n ∧
      G.tableAlgorithm seed time E n bits = some x} = lengthSlice L n := by
  have bound := G.tableAlgorithm_seed_polynomial seed E n
  ext x
  constructor
  · rintro ⟨bits, length, output⟩
    rw [G.tableAlgorithm_take seed time E n (by omega)] at output
    exact G.tableAlgorithm_sound seed time bounded (by
      simp [Nat.min_eq_left (by omega : G.tableAlgorithmSeed seed E n ≤ bits.length)]) output
  · intro member
    obtain ⟨bits, length, output⟩ := G.tableAlgorithm_complete seed time bounded E member
    refine ⟨bits ++ List.replicate (G.tableAlgorithmSeedBound seed E n - bits.length) false, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]; omega
    · rwa [G.tableAlgorithm_append seed time E n length]

include bounded in
theorem polynomial_tableAlgorithm_full_trial_iff (E : LabelEnumeration R) 
    (n : ℕ) (bits : BitString) (length : bits.length = G.tableAlgorithmSeedBound seed E n) :
    (∃ x, G.tableAlgorithm seed time E n bits = some x) ↔ (lengthSlice L n).Nonempty := by
  have bound := G.tableAlgorithm_seed_polynomial seed E n
  rw [G.tableAlgorithm_take seed time E n (by omega)]
  exact G.tableAlgorithm_full_trial_iff seed time bounded E n _ (by
    simp [Nat.min_eq_left (by omega : G.tableAlgorithmSeed seed E n ≤ bits.length)])

end ComplexityOfGenerators.ExactRecursiveGenerators
