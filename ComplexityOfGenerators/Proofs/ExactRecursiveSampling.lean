import ComplexityOfGenerators.Proofs.ExactRecursiveAlgorithm

/-!
# Full finite-seed sampling for Proposition A.23.2

This assembles the base trial and the corrected inverse walk. The resulting
function has exactly the desired length-slice support, succeeds on every full
seed for nonempty slices, and has a polynomial seed bound. The native machine
implementation is a separate obligation: a function with these properties
alone is not a proof of membership in `PG`.
-/

namespace ComplexityOfGenerators.ExactRecursiveGenerators

variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : ExactRecursiveGenerators R)

def baseTrial (time : PolynomialBound) (n : ℕ) (bits : BitString) : Option (Word α) :=
  match G.base.machine.run (generatorData n) bits (time n) with
  | .halted (.accepted y) => some y
  | _ => none

theorem baseTrial_eq_some (time : PolynomialBound) (n : ℕ) (bits : BitString) (y : Word α) :
    G.baseTrial time n bits = some y ↔
      G.base.machine.run (generatorData n) bits (time n) = .halted (.accepted y) := by
  unfold baseTrial
  cases G.base.machine.run (generatorData n) bits (time n) with
  | running c => simp
  | halted result => cases result <;> simp

variable (seed time : PolynomialBound) (bounded : G.base.RunsInTime seed time)

include bounded in
theorem baseTrial_sound {n : ℕ} {bits : BitString} {y : Word α}
    (length : bits.length = seed n) (output : G.baseTrial time n bits = some y) : y ∈ R.bases n := by
  rw [← G.base_language n]
  exact (G.base.machine.trialBound_budget_witness _ _ _ (seed.positive n) (bounded n) y).mpr
    ⟨bits, length, (G.baseTrial_eq_some time n bits y).mp output⟩

include bounded in
theorem baseTrial_complete {n : ℕ} {y : Word α} (member : y ∈ R.bases n) :
    ∃ bits, bits.length = seed n ∧ G.baseTrial time n bits = some y := by
  rw [← G.base_language n] at member
  obtain ⟨bits, length, output⟩ := (G.base.machine.trialBound_budget_witness _ _ _
    (seed.positive n) (bounded n) y).mp member
  exact ⟨bits, length, (G.baseTrial_eq_some time n bits y).mpr output⟩

include bounded in
theorem baseTrial_total {n : ℕ} (nonempty : (lengthSlice L n).Nonempty)
    {bits : BitString} (length : bits.length = seed n) :
    ∃ y, G.baseTrial time n bits = some y := by
  obtain ⟨y, produced⟩ := ((bounded n).2 bits length).mpr ((G.base_nonempty_iff n).mpr nonempty)
  exact ⟨y, (G.baseTrial_eq_some time n bits y).mpr
    (G.base.machine.produces_at_bound _ bits _ y ((bounded n).1 bits length.le) produced)⟩

def algorithmSeed (alphabet : List α) (n : ℕ) : ℕ :=
  seed n + G.walkSeed alphabet n (R.rankBound n)

def algorithm (alphabet : List α) (n : ℕ) (bits : BitString) : Option (Word α) :=
  (G.baseTrial time n (bits.take (seed n))).bind fun y =>
    G.walkTrial alphabet n (R.rankBound n) y (bits.drop (seed n))

theorem algorithm_split_lengths (alphabet : List α) (n : ℕ) {bits : BitString}
    (length : bits.length = G.algorithmSeed seed alphabet n) :
    (bits.take (seed n)).length = seed n ∧
      (bits.drop (seed n)).length = G.walkSeed alphabet n (R.rankBound n) := by
  simp only [algorithmSeed] at length
  simp only [List.length_take, List.length_drop]
  constructor <;> omega

include bounded in
theorem algorithm_sound {alphabet : List α} {n : ℕ} {bits : BitString} {x : Word α}
    (length : bits.length = G.algorithmSeed seed alphabet n)
    (output : G.algorithm seed time alphabet n bits = some x) : x ∈ lengthSlice L n := by
  obtain ⟨baseLength, walkLength⟩ := G.algorithm_split_lengths seed alphabet n length
  unfold algorithm at output
  cases base : G.baseTrial time n (bits.take (seed n)) with
  | none => simp [base] at output
  | some y =>
    have member := G.baseTrial_sound seed time bounded baseLength base
    exact R.walk_sound member.1 (G.walkTrial_sound member.1 walkLength (by simpa [base] using output))

include bounded in
theorem algorithm_complete (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n : ℕ} {x : Word α} (member : x ∈ lengthSlice L n) :
    ∃ bits, bits.length = G.algorithmSeed seed alphabet n ∧
      G.algorithm seed time alphabet n bits = some x := by
  obtain ⟨y, baseMember, path⟩ := R.slice_has_base member
  have target := R.walk_covers_path member baseMember.1.1 path (R.rankBound n)
    (by have := R.ancestor_rank_le (R.slice_subset_ancestors n member); omega)
  obtain ⟨front, frontLength, base⟩ := G.baseTrial_complete seed time bounded baseMember
  obtain ⟨rest, restLength, walk⟩ := G.walkTrial_complete alphabet complete baseMember.1 target
  refine ⟨front ++ rest, ?_, ?_⟩
  · simp [algorithmSeed, frontLength, restLength]
  · simpa [algorithm, ← frontLength, base] using walk

include bounded in
theorem algorithm_total (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n : ℕ} (nonempty : (lengthSlice L n).Nonempty) {bits : BitString}
    (length : bits.length = G.algorithmSeed seed alphabet n) :
    ∃ x, G.algorithm seed time alphabet n bits = some x := by
  obtain ⟨baseLength, walkLength⟩ := G.algorithm_split_lengths seed alphabet n length
  obtain ⟨y, base⟩ := G.baseTrial_total seed time bounded nonempty baseLength
  have member := G.baseTrial_sound seed time bounded baseLength base
  obtain ⟨x, walk⟩ := G.walkTrial_total alphabet complete member.1 (by omega) walkLength
  exact ⟨x, by simpa [algorithm, base] using walk⟩

include bounded in
/-- Exact support of the assembled, executable finite-seed algorithm. -/
theorem algorithm_support (alphabet : List α) (complete : ∀ a, a ∈ alphabet) (n : ℕ) :
    {x | ∃ bits, bits.length = G.algorithmSeed seed alphabet n ∧
      G.algorithm seed time alphabet n bits = some x} = lengthSlice L n := by
  ext x
  exact ⟨fun ⟨_, length, output⟩ => G.algorithm_sound seed time bounded length output,
    G.algorithm_complete seed time bounded alphabet complete⟩

include bounded in
/-- Every full seed succeeds exactly when the target length slice is nonempty. -/
theorem algorithm_full_trial_iff (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    (n : ℕ) (bits : BitString) (length : bits.length = G.algorithmSeed seed alphabet n) :
    (∃ x, G.algorithm seed time alphabet n bits = some x) ↔ (lengthSlice L n).Nonempty :=
  ⟨fun ⟨x, output⟩ => ⟨x, G.algorithm_sound seed time bounded length output⟩,
    fun nonempty => G.algorithm_total seed time bounded alphabet complete nonempty length⟩

/-- Polynomial bound including both the source trial seeds and all selection
and stopping coins. This is a seed bound, not a native running-time claim. -/
noncomputable def algorithmSeedBound (alphabet : List α) : PolynomialBound :=
  PolynomialBound.ofPolynomial (seed.asPolynomial + R.rankBound.asPolynomial *
    (1 + (R.labelCountBound alphabet).asPolynomial * (G.inverseSeed.asPolynomial + 1)))

theorem algorithm_seed_polynomial (alphabet : List α) (n : ℕ) :
    G.algorithmSeed seed alphabet n ≤ G.algorithmSeedBound seed alphabet n := by
  have count := R.label_count_polynomial alphabet n
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    PolynomialBound.asPolynomial_eval, algorithmSeed, walkSeed, searchSeed]
  gcongr

theorem algorithm_append (alphabet : List α) (n : ℕ) {bits : BitString}
    (length : bits.length = G.algorithmSeed seed alphabet n) (extra : BitString) :
    G.algorithm seed time alphabet n (bits ++ extra) = G.algorithm seed time alphabet n bits := by
  obtain ⟨baseLength, walkLength⟩ := G.algorithm_split_lengths seed alphabet n length
  have enough : seed n ≤ bits.length := by simp only [algorithmSeed] at length; omega
  simp only [algorithm, List.take_append_of_le_length enough, List.drop_append_of_le_length enough]
  cases G.baseTrial time n (bits.take (seed n)) with
  | none => rfl
  | some y => exact G.walkTrial_append alphabet n (R.rankBound n) y walkLength extra

theorem algorithm_take (alphabet : List α) (n : ℕ) {bits : BitString}
    (enough : G.algorithmSeed seed alphabet n ≤ bits.length) :
    G.algorithm seed time alphabet n bits =
      G.algorithm seed time alphabet n (bits.take (G.algorithmSeed seed alphabet n)) := by
  have length : (bits.take (G.algorithmSeed seed alphabet n)).length = G.algorithmSeed seed alphabet n :=
    by simp [Nat.min_eq_left enough]
  simpa using G.algorithm_append seed time alphabet n length (bits.drop (G.algorithmSeed seed alphabet n))

include bounded in
/-- Padding to the polynomial budget preserves exact support. -/
theorem polynomial_algorithm_support (alphabet : List α) (complete : ∀ a, a ∈ alphabet) (n : ℕ) :
    {x | ∃ bits, bits.length = G.algorithmSeedBound seed alphabet n ∧
      G.algorithm seed time alphabet n bits = some x} = lengthSlice L n := by
  have bound := G.algorithm_seed_polynomial seed alphabet n
  ext x
  constructor
  · rintro ⟨bits, length, output⟩
    rw [G.algorithm_take seed time alphabet n (by omega)] at output
    exact G.algorithm_sound seed time bounded (by
      simp [Nat.min_eq_left (by omega : G.algorithmSeed seed alphabet n ≤ bits.length)]) output
  · intro member
    obtain ⟨bits, length, output⟩ := G.algorithm_complete seed time bounded alphabet complete member
    refine ⟨bits ++ List.replicate (G.algorithmSeedBound seed alphabet n - bits.length) false, ?_, ?_⟩
    · simp only [List.length_append, List.length_replicate]; omega
    · rwa [G.algorithm_append seed time alphabet n length]

include bounded in
theorem polynomial_algorithm_full_trial_iff (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    (n : ℕ) (bits : BitString) (length : bits.length = G.algorithmSeedBound seed alphabet n) :
    (∃ x, G.algorithm seed time alphabet n bits = some x) ↔ (lengthSlice L n).Nonempty := by
  have bound := G.algorithm_seed_polynomial seed alphabet n
  rw [G.algorithm_take seed time alphabet n (by omega)]
  exact G.algorithm_full_trial_iff seed time bounded alphabet complete n _ (by
    simp [Nat.min_eq_left (by omega : G.algorithmSeed seed alphabet n ≤ bits.length)])

end ComplexityOfGenerators.ExactRecursiveGenerators
