import ComplexityOfGenerators.Proofs.ExactRecursiveSupport
import ComplexityOfGenerators.Foundations.TrialBounds

/-!
# Full native trials of the exact-recursive components

The inverse calls in the bounded walk must test empty fibres without losing
support. The existing full-budget witness theorem and Remark 1 emptiness test
provide precisely these contracts. No new probability or simulation axiom is
needed for an individual call.
-/

namespace ComplexityOfGenerators.ExactRecursiveGenerators

variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}
    (G : ExactRecursiveGenerators R)

theorem base_nonempty_iff (n : ℕ) :
    (G.base.layer n).Nonempty ↔ (lengthSlice L n).Nonempty := by
  rw [G.base_language]
  exact R.bases_nonempty_iff n

/-- Read the result of one explicitly clocked inverse trial. Failure remains
`none`; it does not silently return a default word outside the fibre. -/
def inverseTrial (n : ℕ) (y w : Word α) (bits : BitString) : Option (Word α) :=
  match G.inverse.run { input := y, auxiliary := w, index := n } bits (G.inverseTime n) with
  | .halted (.accepted x) => some x
  | _ => none

theorem inverseTrial_eq_some (n : ℕ) (y w x : Word α) (bits : BitString) :
    G.inverseTrial n y w bits = some x ↔
      G.inverse.run { input := y, auxiliary := w, index := n } bits (G.inverseTime n) =
        .halted (.accepted x) := by
  unfold inverseTrial
  cases G.inverse.run { input := y, auxiliary := w, index := n } bits (G.inverseTime n) with
  | running c => simp
  | halted result => cases result <;> simp

theorem inverseTrial_sound {n : ℕ} {y w x : Word α} (member : y ∈ L)
    {bits : BitString} (length : bits.length = G.inverseSeed n)
    (output : G.inverseTrial n y w bits = some x) : x ∈ R.inverseFibre n y w := by
  rw [← G.inverse_language n y w member]
  apply (G.inverse.trialBound_budget_witness _ _ _ (G.inverseSeed.positive n)
    (G.inverse_time n y w member) x).mpr
  exact ⟨bits, length, (G.inverseTrial_eq_some n y w x bits).mp output⟩

/-- Every word in a fibre has an exact full-budget seed, not just a seed of
unbounded length from the definition of generated language. -/
theorem inverseTrial_complete {n : ℕ} {y w x : Word α} (member : y ∈ L)
    (target : x ∈ R.inverseFibre n y w) :
    ∃ bits, bits.length = G.inverseSeed n ∧ G.inverseTrial n y w bits = some x := by
  rw [← G.inverse_language n y w member] at target
  obtain ⟨bits, length, output⟩ := (G.inverse.trialBound_budget_witness _ _ _
    (G.inverseSeed.positive n) (G.inverse_time n y w member) x).mp target
  exact ⟨bits, length, (G.inverseTrial_eq_some n y w x bits).mpr output⟩

/-- Every full trial succeeds exactly when the fibre is nonempty. This is
stronger than merely having some successful seed for each nonempty fibre. -/
theorem inverseTrial_success_iff {n : ℕ} {y w : Word α} (member : y ∈ L)
    (bits : BitString) (length : bits.length = G.inverseSeed n) :
    (∃ x, G.inverseTrial n y w bits = some x) ↔ (R.inverseFibre n y w).Nonempty := by
  constructor
  · rintro ⟨x, output⟩
    exact ⟨x, G.inverseTrial_sound member length output⟩
  · intro nonempty
    rw [← G.inverse_language n y w member] at nonempty
    have bound := G.inverse_time n y w member
    obtain ⟨x, produced⟩ := (bound.2 bits length).mpr nonempty
    exact ⟨x, (G.inverseTrial_eq_some n y w x bits).mpr
      (G.inverse.produces_at_bound _ bits _ x (bound.1 bits length.le) produced)⟩

theorem inverseTrial_none_iff {n : ℕ} {y w : Word α} (member : y ∈ L)
    (bits : BitString) (length : bits.length = G.inverseSeed n) :
    G.inverseTrial n y w bits = none ↔ R.inverseFibre n y w = ∅ := by
  rw [← Set.not_nonempty_iff_eq_empty, ← G.inverseTrial_success_iff member bits length]
  cases G.inverseTrial n y w bits <;> simp

/-- Below the target length, a label in the polynomial enumeration succeeds
on every full trial. No unproved independence assumption about previous random
choices is needed: the quantifier covers every possible fresh seed. -/
theorem progress_full_trial (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n) (short : y.length < n) :
    ∃ w ∈ SelfReduction.wordsUpTo alphabet (R.labelWidth n), w ≠ [] ∧
      ∀ bits, bits.length = G.inverseSeed n →
        ∃ x, G.inverseTrial n y w bits = some x ∧ R.Up n y x := by
  obtain ⟨w, nonempty, z, zm⟩ := R.ancestor_progress ancestor short
  refine ⟨w, R.inverse_label_mem alphabet complete zm, nonempty, ?_⟩
  intro bits length
  obtain ⟨x, output⟩ := (G.inverseTrial_success_iff ancestor.1 bits length).mpr ⟨z, zm⟩
  exact ⟨x, output, w, nonempty, G.inverseTrial_sound ancestor.1 length output⟩

/-- The number of source-machine transitions allowed for a base trial and at
most `rankBound n` exhaustive inverse searches is bounded by a polynomial.
This does not include the still-needed native orchestration and tape overhead. -/
def sourceTimeBound (alphabet : List α) (baseTime : PolynomialBound) : PolynomialBound :=
  baseTime.add (R.rankBound.mul ((R.labelCountBound alphabet).mul G.inverseTime))

theorem source_time_polynomial (alphabet : List α) (baseTime : PolynomialBound) (n : ℕ) :
    baseTime n + R.rankBound n *
      (SelfReduction.wordsUpTo alphabet (R.labelWidth n)).length * G.inverseTime n ≤
        G.sourceTimeBound alphabet baseTime n := by
  apply le_trans _ (baseTime.add_le (R.rankBound.mul ((R.labelCountBound alphabet).mul G.inverseTime)) n)
  simp only [PolynomialBound.mul_eval]
  have count := R.label_count_polynomial alphabet n
  calc
    baseTime n + R.rankBound n *
        (SelfReduction.wordsUpTo alphabet (R.labelWidth n)).length * G.inverseTime n ≤
        baseTime n + R.rankBound n * (R.labelCountBound alphabet n) * G.inverseTime n := by
      gcongr
    _ = _ := by ring

end ComplexityOfGenerators.ExactRecursiveGenerators
