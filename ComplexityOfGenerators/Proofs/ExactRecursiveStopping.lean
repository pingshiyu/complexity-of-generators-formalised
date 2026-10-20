import ComplexityOfGenerators.Proofs.ExactRecursiveSupport

/-!
# The stopping condition in the printed proof of Proposition A.23.2

A length-preserving reduction can take a positive-certificate word to a
zero-certificate word of the same length. Returning immediately after sampling
that base misses the original word. This file checks that obstruction on a
concrete self-reduction of the universal binary language.

This is a counterexample to the printed *algorithm's support argument*, not
to the proposition. `bounded_walk_support` permits an optional stop and handles
this example without strengthening the self-reduction hypotheses.
-/

namespace ComplexityOfGenerators.SelfReduction

namespace StoppingExample

def rank : BitString → ℕ
  | true :: _ => 1
  | _ => 0

def reduce : BitString → BitString → BitString
  | [], _ => []
  | _ :: tail, _ => false :: tail

@[simp] theorem rank_reduce (x w : BitString) : rank (reduce x w) = 0 := by
  cases x <;> rfl

@[simp] theorem length_reduce (x w : BitString) : (reduce x w).length = x.length := by
  cases x <;> rfl

theorem rank_le_one (x : BitString) : rank x ≤ 1 := by
  cases x with
  | nil => decide
  | cons bit tail => cases bit <;> simp [rank]

/-- On a word starting with `true`, all one-bit words are certificates.
On every other word the only certificate is `[]`. Reduction changes the
first bit to `false`, retaining the original word length. -/
def reduction : SelfReduction (Set.univ : Language Bool) where
  certificates := fun x => {c | c.length = rank x}
  rank := rank
  width := rank
  reduce := reduce
  certifies := by
    intro x
    exact ⟨fun _ => ⟨List.replicate (rank x) false, by simp⟩, fun _ => Set.mem_univ x⟩
  certificate_length := fun _ _ h => h
  split := by
    intro x c
    constructor
    · intro length
      exact ⟨c, [], length, by simp, by simp⟩
    · rintro ⟨w, d, length, tail, rfl⟩
      change d.length = rank (reduce x w) at tail
      simp only [rank_reduce, List.length_eq_zero_iff] at tail
      simpa [tail] using length
  positive := fun _ => Iff.rfl
  length_reduce := fun x w => (length_reduce x w).le
  rank_reduce := by intro x w; simp
  rankBound := ⟨1, 0, by decide⟩
  rank_le := rank_le_one
  logCoefficient := 0
  logConstant := 1
  width_le := by intro x; simpa using rank_le_one x

theorem iterated_preserves_length {x w y : BitString} (path : reduction.Iterated x w y) :
    y.length = x.length := by
  induction path with
  | single x w _ => exact length_reduce x w
  | more x w rest y _ _ _ ih => exact ih.trans (length_reduce x w)

theorem ancestor_length {n : ℕ} {y : BitString} (ancestor : y ∈ reduction.ancestors n) :
    y.length = n := by
  rcases ancestor.2 with length | ⟨x, xm, w, _, path⟩
  · exact length
  · exact (iterated_preserves_length path).trans xm.2

/-- The paper's mandatory stopping rule, with a fuel parameter only to make
the algorithm's set of possible outputs a total Lean definition. -/
def printedWalk (n : ℕ) : ℕ → BitString → Language Bool
  | 0, y => {x | x = y ∧ y.length = n}
  | fuel + 1, y => if y.length = n then {y} else
      {x | ∃ z, reduction.Up n y z ∧ x ∈ printedWalk n fuel z}

theorem printedWalk_at_length (n fuel : ℕ) {y : BitString} (length : y.length = n) :
    printedWalk n fuel y = {y} := by
  cases fuel with
  | zero => ext x; simp [printedWalk, length]
  | succ fuel => simp [printedWalk, length]

/-- `[true]` belongs to the target slice but cannot be emitted under the
printed mandatory stopping rule, regardless of the fuel allowance. -/
theorem printed_algorithm_misses_member (fuel : ℕ) :
    [true] ∈ lengthSlice (Set.univ : Language Bool) 1 ∧
      ¬ ∃ y ∈ reduction.bases 1, [true] ∈ printedWalk 1 fuel y := by
  refine ⟨⟨Set.mem_univ _, rfl⟩, ?_⟩
  rintro ⟨y, base, generated⟩
  rw [printedWalk_at_length 1 fuel (ancestor_length base.1)] at generated
  have equal : [true] = y := generated
  have zero := base.2
  simp [← equal, reduction, rank] at zero

/-- The corrected bounded support theorem includes the omitted word. -/
theorem optional_stop_covers_member :
    ∃ y ∈ reduction.bases 1, [true] ∈ reduction.walkOutputs 1 (reduction.rankBound 1) y := by
  have member : [true] ∈ lengthSlice (Set.univ : Language Bool) 1 := ⟨Set.mem_univ _, rfl⟩
  rw [← reduction.bounded_walk_support 1] at member
  exact member

end StoppingExample
end ComplexityOfGenerators.SelfReduction
