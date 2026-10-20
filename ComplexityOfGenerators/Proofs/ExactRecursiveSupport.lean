import ComplexityOfGenerators.Proofs.SelfReduction
import Mathlib.Data.Nat.Log

/-!
# Bounded inverse walks for Proposition A.23.2

This file proves the support and progress arguments for a corrected algorithm.
At a length-`n` word the algorithm may either stop or continue along a nonempty
inverse label. Stopping unconditionally at the first length-`n` word, as in the
printed proof, need not give full support when reductions preserve word length.

These are semantic and resource-counting lemmas, not a native loop compiler.
-/

namespace ComplexityOfGenerators.SelfReduction

variable {α : Type} {L : Language α} (R : SelfReduction L)

/-- One allowed upward move, retaining the ancestor invariant and excluding
the empty labels that need not increase certificate length. -/
def Up (n : ℕ) (y x : Word α) : Prop :=
  ∃ w, w ≠ [] ∧ x ∈ R.inverseFibre n y w

theorem up_iff {n : ℕ} {y x : Word α} :
    R.Up n y x ↔ x ∈ R.ancestors n ∧ R.Step x y := by
  constructor
  · rintro ⟨w, nonempty, ancestor, reduction, length⟩
    have positive : 0 < R.width x := by
      have := List.length_pos_iff.mpr nonempty
      omega
    exact ⟨ancestor, w, positive, length, reduction⟩
  · rintro ⟨ancestor, w, positive, length, reduction⟩
    refine ⟨w, ?_, ancestor, reduction, length⟩
    intro empty
    simp [empty] at length
    omega

/-- All stopping outputs of an inverse walk of at most `fuel` steps. The
singleton branch represents a random choice to stop, not a mandatory stop. -/
def walkOutputs (n : ℕ) : ℕ → Word α → Language α
  | 0, y => {x | x = y ∧ y.length = n}
  | fuel + 1, y => {x | (x = y ∧ y.length = n) ∨
      ∃ z, R.Up n y z ∧ x ∈ walkOutputs n fuel z}

theorem walk_stop (n fuel : ℕ) {y : Word α} (length : y.length = n) :
    y ∈ R.walkOutputs n fuel y := by
  cases fuel with
  | zero => exact ⟨rfl, length⟩
  | succ fuel => exact Or.inl ⟨rfl, length⟩

theorem walk_sound {n fuel : ℕ} {y x : Word α} (ancestor : y ∈ R.ancestors n)
    (generated : x ∈ R.walkOutputs n fuel y) : x ∈ lengthSlice L n := by
  induction fuel generalizing y with
  | zero => obtain ⟨rfl, length⟩ := generated; exact ⟨ancestor.1, length⟩
  | succ fuel ih =>
    rcases generated with ⟨rfl, length⟩ | ⟨z, step, rest⟩
    · exact ⟨ancestor.1, length⟩
    · exact ih (R.up_iff.mp step).1 rest

/-- Enough remaining certificate rank gives enough fuel to reverse any
particular reduction path, including paths through length-preserving steps. -/
theorem walk_covers_path {n : ℕ} {x y : Word α} (member : x ∈ lengthSlice L n)
    (ym : y ∈ L) (path : R.Path x y) (fuel : ℕ)
    (enough : R.rank x ≤ R.rank y + fuel) : x ∈ R.walkOutputs n fuel y := by
  induction path generalizing fuel with
  | refl => exact R.walk_stop n fuel member.2
  | @tail z y initialPath step ih =>
    have zm := R.step_mem step ym
    have za : z ∈ R.ancestors n := R.mem_ancestors_iff.mpr ⟨zm, x, member, initialPath⟩
    have decrease := R.step_rank_lt step
    have lower := R.path_rank_le initialPath
    cases fuel with
    | zero => omega
    | succ fuel =>
      exact Or.inr ⟨z, R.up_iff.mpr ⟨za, step⟩, ih zm fuel (by omega)⟩

/-- A bounded inverse walk from the base language has exactly the desired
support. This is the language part of Proposition A.23.2, not `PG` membership. -/
theorem bounded_walk_support (n : ℕ) :
    {x | ∃ y ∈ R.bases n, x ∈ R.walkOutputs n (R.rankBound n) y} = lengthSlice L n := by
  ext x
  constructor
  · rintro ⟨y, base, generated⟩
    exact R.walk_sound base.1 generated
  · intro member
    obtain ⟨y, base, path⟩ := R.slice_has_base member
    refine ⟨y, base, R.walk_covers_path member base.1.1 path _ ?_⟩
    have rank := R.ancestor_rank_le (R.slice_subset_ancestors n member)
    omega

/-- Below length `n`, every ancestor has a permitted upward step. -/
theorem up_progress {n : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n)
    (short : y.length < n) : ∃ z, R.Up n y z := by
  obtain ⟨w, nonempty, z, member⟩ := R.ancestor_progress ancestor short
  exact ⟨z, w, nonempty, member⟩

/-- There is no dead end below length `n`; sufficient fuel always permits a
length-`n` output from every sampled base, not just from specially chosen bases. -/
theorem walk_nonempty {n fuel : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n)
    (enough : R.rankBound n ≤ R.rank y + fuel) : (R.walkOutputs n fuel y).Nonempty := by
  induction fuel generalizing y with
  | zero =>
    have length := R.ancestor_length_le ancestor
    have equal : y.length = n := by
      by_contra different
      obtain ⟨z, w, nonempty, member⟩ := R.up_progress ancestor (by omega)
      have increase := R.inverse_rank_lt nonempty member
      have bound := R.ancestor_rank_le member.1
      omega
    exact ⟨y, R.walk_stop n 0 equal⟩
  | succ fuel ih =>
    by_cases length : y.length = n
    · exact ⟨y, R.walk_stop n (fuel + 1) length⟩
    · obtain ⟨z, step⟩ := R.up_progress ancestor (by have := R.ancestor_length_le ancestor; omega)
      obtain ⟨za, reduction⟩ := R.up_iff.mp step
      have increase := R.step_rank_lt reduction
      obtain ⟨x, generated⟩ := ih za (by omega)
      exact ⟨x, Or.inr ⟨z, step, generated⟩⟩

/-- A sequence of successful inverse calls consumes at least one unit of rank
per call. This is the termination bound for every possible choice of outputs. -/
theorem up_chain_rank (n : ℕ) (states : ℕ → Word α) (steps : ℕ)
    (chain : ∀ i < steps, R.Up n (states i) (states (i + 1))) :
    R.rank (states 0) + steps ≤ R.rank (states steps) := by
  induction steps with
  | zero => omega
  | succ steps ih =>
    have previous := ih (fun i hi => chain i (by omega))
    have increase := R.step_rank_lt (R.up_iff.mp (chain steps (by omega))).2
    omega

theorem up_chain_length_bound (n : ℕ) (states : ℕ → Word α) (steps : ℕ)
    (initial : states 0 ∈ R.ancestors n)
    (chain : ∀ i < steps, R.Up n (states i) (states (i + 1))) : steps ≤ R.rankBound n := by
  have finalAncestor : states steps ∈ R.ancestors n := by
    cases steps with
    | zero => exact initial
    | succ steps => exact (R.up_iff.mp (chain steps (by omega))).1
  have bound := R.ancestor_rank_le finalAncestor
  have increase := R.up_chain_rank n states steps chain
  omega

/-- The common label-length bound for all ancestors at index `n`. -/
def labelWidth (n : ℕ) : ℕ := R.logCoefficient * Nat.log 2 (n + 1) + R.logConstant

theorem ancestor_width_le {n : ℕ} {x : Word α} (ancestor : x ∈ R.ancestors n) :
    R.width x ≤ R.labelWidth n := by
  apply (R.width_le x).trans
  exact Nat.add_le_add_right (Nat.mul_le_mul_left _
    (Nat.log_mono_right (Nat.add_le_add_right (R.ancestor_length_le ancestor) 1))) _

/-- A simple exhaustive enumeration, including `[]`. It works for an empty
alphabet as well; no choice of a default alphabet symbol is needed. -/
def wordsUpTo (alphabet : List α) : ℕ → List (Word α)
  | 0 => [[]]
  | k + 1 => [] :: alphabet.flatMap (fun a => (wordsUpTo alphabet k).map (a :: ·))

theorem mem_wordsUpTo (alphabet : List α) (complete : ∀ a, a ∈ alphabet) (k : ℕ)
    (word : Word α) : word ∈ wordsUpTo alphabet k ↔ word.length ≤ k := by
  induction k generalizing word with
  | zero => simp [wordsUpTo]
  | succ k ih =>
    cases word with
    | nil => simp [wordsUpTo]
    | cons a word => simp [wordsUpTo, ih, complete]

theorem wordsUpTo_length_le (alphabet : List α) (k : ℕ) :
    (wordsUpTo alphabet k).length ≤ (alphabet.length + 1) ^ (k + 1) := by
  induction k with
  | zero => simp [wordsUpTo]
  | succ k ih =>
    have one : 1 ≤ (alphabet.length + 1) ^ (k + 1) := one_le_pow₀ (by omega)
    have size : (wordsUpTo alphabet (k + 1)).length =
        1 + alphabet.length * (wordsUpTo alphabet k).length := by
      simp [wordsUpTo, List.length_flatMap, Nat.add_comm]
    rw [size, pow_succ]
    nlinarith

/-- A polynomial bound for the size of the label enumeration. The exponent
uses `|alphabet| + 1`, a coarse bound on its binary logarithm. -/
def labelCountBound (alphabet : List α) : PolynomialBound where
  coefficient := 2 ^ ((alphabet.length + 1) * (R.logConstant + 1))
  degree := (alphabet.length + 1) * R.logCoefficient
  coefficient_pos := pow_pos (by decide) _

theorem label_count_polynomial (alphabet : List α) (n : ℕ) :
    (wordsUpTo alphabet (R.labelWidth n)).length ≤ R.labelCountBound alphabet n := by
  apply (wordsUpTo_length_le alphabet _).trans
  have alphabetBound : alphabet.length + 1 ≤ 2 ^ (alphabet.length + 1) :=
    (Nat.lt_two_pow_self).le
  have logBound : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  calc
    (alphabet.length + 1) ^ (R.labelWidth n + 1) ≤
        (2 ^ (alphabet.length + 1)) ^ (R.labelWidth n + 1) := pow_le_pow_left' alphabetBound _
    _ = 2 ^ ((alphabet.length + 1) * (R.logConstant + 1)) *
        (2 ^ Nat.log 2 (n + 1)) ^ ((alphabet.length + 1) * R.logCoefficient) := by
      simp only [← pow_mul, ← pow_add, labelWidth]
      congr 1
      ring
    _ ≤ R.labelCountBound alphabet n := by
      exact Nat.mul_le_mul_left _ (pow_le_pow_left' logBound _)

/-- Every nonempty inverse label belongs to the polynomial-size search table. -/
theorem inverse_label_mem (alphabet : List α) (complete : ∀ a, a ∈ alphabet)
    {n : ℕ} {x y w : Word α} (member : x ∈ R.inverseFibre n y w) :
    w ∈ wordsUpTo alphabet (R.labelWidth n) := by
  apply (mem_wordsUpTo alphabet complete _ _).mpr
  rw [member.2.2]
  exact R.ancestor_width_le member.1

end ComplexityOfGenerators.SelfReduction
