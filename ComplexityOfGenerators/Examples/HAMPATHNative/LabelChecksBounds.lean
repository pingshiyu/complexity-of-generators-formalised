import ComplexityOfGenerators.Examples.HAMPATHNative.LabelChecks
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.ComparisonBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.LabelChecks

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem require_bound {O : Type} (expected : Bool) (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((require (O := O) expected).eval s) budget ∧ (require (O := O) expected).cost s ≤ 3 * budget + 1 := by
  constructor
  · rw [require_eval]
    apply sizes.update 16
    split
    · exact sizes 16
    · simp
  · have size := sizes 16
    simp only [require, Routine.branch]
    split <;> simp [Routine.skip, Routine.ofLocal, Local.ticks, Routine.clear] <;> omega

theorem bits_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((bits (O := O)).eval s) budget ∧ (bits (O := O)).cost s ≤ 40 * (budget + 1) := by
  have lengths := congrArg List.length
    (show (s 25).takeWhile isBit ++ (s 25).dropWhile isBit = s 25 from List.takeWhile_append_dropWhile)
  simp only [List.length_append] at lengths
  have source := sizes 25
  constructor
  · rw [bits_eval]
    apply (((sizes.clear 23).update 21 _ (by omega)).update 22 _ (by simp only [List.length_reverse]; omega)).update 16
    split
    · exact sizes 16
    · simp
  · let a := (Routine.assign (O := O) 25 21 23 (by decide) (by decide) (by decide) id).eval s
    let b := (Routine.clear (O := O) 22).eval a
    let c := (Routine.transferWhile (O := O) 21 22 (by decide) isBit id).eval b
    have flagSize := sizes 16
    have copySize := sizes 21
    have targetSize := sizes 22
    have scratchSize := sizes 23
    have assignCost : (Routine.assign (O := O) 25 21 23 (by decide) (by decide) (by decide) id).cost s ≤ 20 * budget + 3 := by
      rw [Routine.assign_cost]; omega
    have sourceWord : b 21 = s 25 := by simp [b, a, Routine.clear, Routine.assign_eval]
    have clearCost : (Routine.clear (O := O) 22).cost a ≤ 3 * budget := by
      simp only [Routine.clear]
      have same : a 22 = s 22 := by simp [a, Routine.assign_eval]
      rw [same]
      omega
    have transferCost : (Routine.transferWhile (O := O) 21 22 (by decide) isBit id).cost b ≤ 6 * budget := by
      change 6 * ((b 21).takeWhile isBit).length ≤ _
      rw [sourceWord]
      omega
    have finalCost : (Routine.branch (O := O) 21 fun rest => if rest.isSome then Routine.clear 16 else Routine.skip).cost c ≤
        3 * budget + 1 := by
      have validSame : c 16 = s 16 := by simp [c, b, a, Routine.transferWhile, Routine.clear, Routine.assign_eval]
      simp only [Routine.branch]
      split <;> simp [Routine.clear, Routine.skip, Routine.ofLocal, Local.ticks, validSame] <;> omega
    unfold bits
    change (Routine.assign (O := O) 25 21 23 (by decide) (by decide) (by decide) id).cost s + 1 +
      ((Routine.clear (O := O) 22).cost a + 1 +
        ((Routine.transferWhile (O := O) 21 22 (by decide) isBit id).cost b + 1 +
          (Routine.branch (O := O) 21 fun rest => if rest.isSome then Routine.clear 16 else Routine.skip).cost c)) ≤ _
    omega

theorem marked_bound {O : Type} (test : Routine Symbol O 32) (expected : Bool) (s : Store) (budget : ℕ)
    (bounded : StoreBound (test.eval s) budget) (cost : test.cost s ≤ 80 * (budget + 1)) :
    StoreBound ((test.seq (require expected)).eval s) budget ∧
      (test.seq (require expected)).cost s ≤ 90 * (budget + 1) := by
  obtain ⟨finalBound, finalCost⟩ := require_bound (O := O) expected (test.eval s) budget bounded
  exact ⟨finalBound, by change test.cost s + 1 + _ ≤ _; omega⟩

theorem lengthCheck_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((lengthCheck (O := O)).eval s) budget ∧ (lengthCheck (O := O)).cost s ≤ 90 * (budget + 1) := by
  unfold lengthCheck
  exact marked_bound (LengthTest.routine lengthSlots (.bit true)) true s budget
    (sizes.lengthTest lengthSlots (.bit true) positive) (LengthTest.routine_cost _ _ _ _ sizes)

theorem belowCheck_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((belowCheck (O := O)).eval s) budget ∧ (belowCheck (O := O)).cost s ≤ 90 * (budget + 1) := by
  have testBound := sizes.strictCompare (O := O) belowSlots (.bit true) positive
  unfold belowCheck
  exact marked_bound (RationalSelection.Compare.routine belowSlots (.bit true)) true s budget testBound
    (RationalSelection.Compare.routine_cost _ _ _ _ sizes)

theorem differentCheck_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((differentCheck (O := O)).eval s) budget ∧ (differentCheck (O := O)).cost s ≤ 90 * (budget + 1) := by
  unfold differentCheck
  exact marked_bound (LengthTest.routine equalSlots (.bit true)) false s budget
    (sizes.lengthTest equalSlots (.bit true) positive) (LengthTest.routine_cost _ _ _ _ sizes)

theorem routine_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((routine (O := O)).eval s) budget ∧ (routine (O := O)).cost s ≤ 320 * (budget + 1) := by
  let a := (bits (O := O)).eval s
  let b := (lengthCheck (O := O)).eval a
  let c := (belowCheck (O := O)).eval b
  obtain ⟨aBound, aCost⟩ := bits_bound (O := O) s budget sizes
  obtain ⟨bBound, bCost⟩ := lengthCheck_bound (O := O) a budget positive aBound
  obtain ⟨cBound, cCost⟩ := belowCheck_bound (O := O) b budget positive bBound
  obtain ⟨dBound, dCost⟩ := differentCheck_bound (O := O) c budget positive cBound
  exact ⟨dBound, by change (bits (O := O)).cost s + 1 + ((lengthCheck (O := O)).cost a + 1 +
    ((belowCheck (O := O)).cost b + 1 + (differentCheck (O := O)).cost c)) ≤ _; omega⟩

theorem require_randomFree {O : Type} (expected : Bool) : Command.RandomFree (require (O := O) expected).command := by
  simp only [require, Routine.randomFree_branch]
  intro flag
  split <;> simp

theorem routine_randomFree {O : Type} : Command.RandomFree (routine (O := O)).command := by
  have bitPure : Command.RandomFree (bits (O := O)).command := by
    simp only [bits, Routine.randomFree_seq]
    refine ⟨Routine.randomFree_assign _ _ _ _ _ _ _, Routine.randomFree_clear _, Routine.randomFree_transferWhile _ _ _ _ _, ?_⟩
    apply (Routine.randomFree_branch _ _).mpr
    intro rest
    split <;> simp
  have lengthPure : Command.RandomFree (lengthCheck (O := O)).command := by
    simp [lengthCheck, require_randomFree, LengthTest.routine, LengthTest.setup, DrainPair.routine]
  have belowPure : Command.RandomFree (belowCheck (O := O)).command := by
    simp [belowCheck, require_randomFree, RationalSelection.Compare.routine, RationalSelection.Compare.setup, DrainPair.routine]
  have differentPure : Command.RandomFree (differentCheck (O := O)).command := by
    simp [differentCheck, require_randomFree, LengthTest.routine, LengthTest.setup, DrainPair.routine]
  exact .seq bitPure (.seq lengthPure (.seq belowPure differentPure))

end ComplexityOfGenerators.Examples.HAMPATH.Native.LabelChecks
