import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.Native
import ComplexityOfGenerators.Simulation.WordStack.GrowingRoutine

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem rowRoutine_bound {O : Type} (s : Store) (budget size : ℕ)
    (sizes : StoreBound s budget) (width : (s 1).length ≤ size) :
    StoreBound ((rowRoutine (O := O)).eval s) (budget+size+1) := by
  rw [rowRoutine_eval_store]
  apply (((((((sizes.mono (by omega)).update 0 _ ?_).update 3 _ ?_).update 5 _ ?_).clear 8).clear 9).clear 10).clear 11 |>.clear 12 |>.clear 13 |>.clear 14
  · simp only [List.length_drop]
    exact (Nat.sub_le _ _).trans ((sizes 0).trans (by omega))
  · simp only [List.length_tail]
    exact (Nat.sub_le _ _).trans ((sizes 3).trans (by omega))
  · simp only [List.length_append, List.length_reverse, InsertAt.insertAt_length, List.length_take]
    have output := sizes 5
    have take := Nat.min_le_left (s 1).length (s 0).length
    omega

theorem rowPrepare_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((rowPrepare (O := O)).eval s) budget := by
  let a := (Routine.clearMany (O := O) [9,10]).eval s
  let b := (Routine.assign (O := O) 1 8 14 (by decide) (by decide) (by decide) id).eval a
  let c := (Blocks.routine (O := O) 8 0 9 (by decide) (by decide)).eval b
  have aBound : StoreBound a budget := sizes.clearMany _
  have bBound : StoreBound b budget := aBound.assign _ _ _ _ _ _ _
  have bEmpty : b 9 = [] := by simp [b,a,Routine.assign_eval,Routine.clearMany_eval]
  have cBound : StoreBound c budget := bBound.block _ _ _ (by decide) (by decide) (by decide) bEmpty
  have ten : c 10 = [] := by simp [c,b,a,Blocks.routine_eval,Routine.assign_eval,Routine.clearMany_eval]
  change StoreBound ((Routine.transfer (O := O) 9 10 (by decide) id).eval c) budget
  rw [Routine.transfer]
  apply (cBound.clear 9).update 10
  simpa [ten] using cBound 9

theorem rowPrepare_cost {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (rowPrepare (O := O)).cost s ≤ 120*(budget+1) := by
  let a := (Routine.clearMany (O := O) [9,10]).eval s
  let b := (Routine.assign (O := O) 1 8 14 (by decide) (by decide) (by decide) id).eval a
  let c := (Blocks.routine (O := O) 8 0 9 (by decide) (by decide)).eval b
  have clearing := Routine.clearMany_cost (O := O) [9,10] s budget (fun j _ => sizes j)
  have aBound : StoreBound a budget := sizes.clearMany _
  have copyCost : (Routine.assign (O := O) 1 8 14 (by decide) (by decide) (by decide) id).cost a ≤ 23*budget+4 := by
    have one := aBound 1
    have eight := aBound 8
    have fourteen := aBound 14
    simp only [Routine.assign_cost]
    omega
  have bBound : StoreBound b budget := aBound.assign _ _ _ _ _ _ _
  have blockCost := Blocks.routine_cost (O := O) (8 : Fin 16) 0 9 (by decide) (by decide) b
  have blockClock := bBound 8
  have cNine : (c 9).length ≤ budget := by
    simp [c,Blocks.routine_eval,b,a,Routine.assign_eval,Routine.clearMany_eval]
    exact Or.inr (sizes 0)
  change (Routine.clearMany (O := O) [9,10]).cost s+1+
    ((Routine.assign (O := O) 1 8 14 (by decide) (by decide) (by decide) id).cost a+1+
      ((Blocks.routine (O := O) 8 0 9 (by decide) (by decide)).cost b+1+6*(c 9).length)) ≤ _
  simp only [List.length_cons,List.length_nil] at clearing
  omega

theorem rowRoutine_cost {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (rowRoutine (O := O)).cost s ≤ 1000*(budget+1) := by
  let a := (rowPrepare (O := O)).eval s
  let b := (insertColumn (O := O)).eval a
  let c := (Routine.transfer (O := O) 10 5 (by decide) id).eval b
  have aBound : StoreBound a budget := rowPrepare_bound s budget sizes
  have first := rowPrepare_cost (O := O) s budget sizes
  have middle : (insertColumn (O := O)).cost a ≤ 1+60*(budget+2) := by
    rw [insertColumn_cost]
    exact Nat.add_le_add_left (InsertAt.routine_cost _ _ _ a budget aBound) 1
  have bBound : StoreBound b (budget+1) := by
    dsimp only [b]
    rw [insertColumn_eval]
    exact InsertAt.routine_bound _ _ _ a budget aBound
  have row := bBound 10
  change (rowPrepare (O := O)).cost s+1+((insertColumn (O := O)).cost a+1+
    (6*(b 10).length+1+1)) ≤ _
  omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert
