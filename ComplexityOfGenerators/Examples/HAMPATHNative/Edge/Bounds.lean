import ComplexityOfGenerators.Examples.HAMPATHNative.Edge.Basic
import ComplexityOfGenerators.Examples.HAMPATHNative.StateBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Edge

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem prepare_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((prepare (O := O)).eval s) (budget + 1) ∧
      (prepare (O := O)).cost s ≤ 110 * (budget + 2) := by
  let a := (Routine.assign (O := O) 24 2 9 (by decide) (by decide) (by decide) id).eval s
  let b := (header (O := O)).eval a
  have aBound : StoreBound a budget := sizes.assign 24 2 9 (by decide) (by decide) (by decide) id
  have bBound : StoreBound b (budget + 1) := header_bound a budget aBound
  have finalBound := bBound.assign (O := O) 26 21 23 (by decide) (by decide) (by decide) id
  have first : (Routine.assign (O := O) 24 2 9 (by decide) (by decide) (by decide) id).cost s ≤ 20 * budget + 3 := by
    rw [Routine.assign_cost]
    have := sizes 2
    have := sizes 9
    have := sizes 24
    omega
  have parseCost := header_cost (O := O) a budget aBound
  have last : (Routine.assign (O := O) 26 21 23 (by decide) (by decide) (by decide) id).cost b ≤ 20 * (budget + 1) + 3 := by
    rw [Routine.assign_cost]
    have := bBound 21
    have := bBound 23
    have := bBound 26
    omega
  unfold prepare
  refine ⟨finalBound, ?_⟩
  change (Routine.assign (O := O) 24 2 9 (by decide) (by decide) (by decide) id).cost s + 1 +
    ((header (O := O)).cost a + 1 + (Routine.assign (O := O) 26 21 23 (by decide) (by decide) (by decide) id).cost b) ≤ _
  omega

theorem column_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((column (O := O)).eval s) budget ∧ (column (O := O)).cost s ≤ 40 * (budget + 1) := by
  constructor
  · rw [column_eval]
    have dropped : ((s 2).drop (s 28).length).length ≤ budget := by
      simp only [List.length_drop]
      have bound := sizes 2
      omega
    exact (((sizes.clear 23).clear 22).update 2 _ dropped).clear 20
  · let a := (Routine.clear (O := O) 20).eval s
    let b := (Routine.assign (O := O) 28 22 23 (by decide) (by decide) (by decide) id).eval a
    let c := (Blocks.routine (O := O) 22 2 20 (by decide) (by decide)).eval b
    have aBound : StoreBound a budget := sizes.clear 20
    have bBound : StoreBound b budget := aBound.assign 28 22 23 (by decide) (by decide) (by decide) id
    have bEmpty : b 20 = [] := by simp [b, a, Routine.assign_eval, Routine.clear]
    have cBound : StoreBound c budget := bBound.block 22 2 20 (by decide) (by decide) (by decide) bEmpty
    have copying : (Routine.assign (O := O) 28 22 23 (by decide) (by decide) (by decide) id).cost a ≤ 20 * budget + 3 := by
      rw [Routine.assign_cost]
      have := aBound 22
      have := aBound 23
      have := aBound 28
      omega
    have blocks := Blocks.routine_cost (O := O) (22 : Fin 32) 2 20 (by decide) (by decide) b
    have source := sizes 20
    have clock := bBound 22
    have erased := cBound 20
    unfold column
    change 3 * (s 20).length + 1 +
      ((Routine.assign (O := O) 28 22 23 (by decide) (by decide) (by decide) id).cost a + 1 +
        ((Blocks.routine (O := O) 22 2 20 (by decide) (by decide)).cost b + 1 + 3 * (c 20).length)) ≤ _
    omega

theorem headCheck_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((headCheck (O := O)).eval s) budget ∧ (headCheck (O := O)).cost s ≤ 3 * budget + 1 := by
  constructor
  · rw [headCheck_eval]
    apply sizes.update 16
    split
    · exact sizes 16
    · simp
  · have size := sizes 16
    simp only [headCheck, Routine.branch]
    split <;> simp [Routine.skip, Routine.ofLocal, Local.ticks, Routine.clear] <;> omega

theorem query_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((query (O := O)).eval s) (budget + 1) ∧ (query (O := O)).cost s ≤ 200 * (budget + 2)^2 := by
  let a := (prepare (O := O)).eval s
  let b := (rows (O := O)).eval a
  let c := (column (O := O)).eval b
  obtain ⟨aBound, aCost⟩ := prepare_bound (O := O) s budget sizes
  obtain ⟨bBound, bCost⟩ := rows_bound (O := O) a (budget + 1) aBound
  obtain ⟨cBound, cCost⟩ := column_bound (O := O) b (budget + 1) bBound
  obtain ⟨dBound, dCost⟩ := headCheck_bound (O := O) c (budget + 1) cBound
  refine ⟨dBound, ?_⟩
  have rowsClock := aBound 21
  change (a 21).length ≤ budget + 1 at rowsClock
  change (prepare (O := O)).cost s + 1 + ((rows (O := O)).cost a + 1 +
    ((column (O := O)).cost b + 1 + (headCheck (O := O)).cost c)) ≤ _
  nlinarith only [aCost, bCost, cCost, dCost, rowsClock,
    Nat.mul_le_mul_right (50 * (budget + 2)) rowsClock]

theorem query_randomFree {O : Type} : Command.RandomFree (query (O := O)).command := by
  have prepared : Command.RandomFree (prepare (O := O)).command := by
    simp [prepare, header, headerExtract, headerSetup, headerClock]
  have scan : Command.RandomFree (column (O := O)).command := by simp [column, Blocks.routine, Blocks.body]
  have check : Command.RandomFree (headCheck (O := O)).command := by
    simp only [headCheck, Routine.randomFree_branch]
    intro head
    split <;> simp
  exact .seq prepared (.seq rows_randomFree (.seq scan check))

end ComplexityOfGenerators.Examples.HAMPATH.Native.Edge
