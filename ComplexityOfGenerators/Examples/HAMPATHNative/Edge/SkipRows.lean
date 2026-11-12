import ComplexityOfGenerators.Examples.HAMPATHNative.Cell
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Edge

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def dropRow {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 20).seq
    ((Routine.assign 27 22 23 (by decide) (by decide) (by decide) id).seq
      ((Blocks.routine 22 2 20 (by decide) (by decide)).seq (Routine.clear 20)))

theorem dropRow_eval {O : Type} (s : Store) :
    (dropRow (O := O)).eval s = Function.update (Function.update (Function.update (Function.update s
      23 []) 22 []) 2 ((s 2).drop (s 27).length)) 20 [] := by
  simp only [dropRow, Routine.seq, Routine.clear, Routine.assign_eval,
    Blocks.routine_eval (22 : Fin 32) 2 20 (by decide) (by decide) (by decide)]
  funext j
  by_cases word : j = 2 <;> by_cases buffer : j = 20 <;> by_cases clock : j = 22 <;> by_cases scratch : j = 23 <;>
    simp [Function.update_apply, word, buffer, clock, scratch]

theorem dropRow_frame {O : Type} (s : Store) (j : Fin 32)
    (word : j ≠ 2) (buffer : j ≠ 20) (clock : j ≠ 22) (scratch : j ≠ 23) :
    (dropRow (O := O)).eval s j = s j := by simp [dropRow_eval, word, buffer, clock, scratch]

theorem dropRow_clock {O : Type} (s : Store) : (dropRow (O := O)).eval s 21 = s 21 :=
  dropRow_frame s 21 (by decide) (by decide) (by decide) (by decide)

def counted {O : Type} : Routine Symbol O 32 := Routine.counted 21 dropRow

theorem counted_values {O : Type} (s : Store) :
    (counted (O := O)).eval s 2 = (s 2).drop (s 27).length ∧
    (counted (O := O)).eval s 27 = s 27 ∧ (counted (O := O)).eval s 16 = s 16 ∧
    (counted (O := O)).eval s 21 = (s 21).tail := by
  simp [counted, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop, dropRow_eval]

theorem iterate_values {O : Type} (s : Store) (count : ℕ) :
    ((counted (O := O)).eval^[count] s) 2 = (s 2).drop (count * (s 27).length) ∧
    ((counted (O := O)).eval^[count] s) 27 = s 27 ∧
    ((counted (O := O)).eval^[count] s) 16 = s 16 ∧
    ((counted (O := O)).eval^[count] s) 21 = (s 21).drop count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      have next := counted_values (O := O) ((counted (O := O)).eval^[count] s)
      rw [ih.1, ih.2.1, ih.2.2.1, ih.2.2.2] at next
      simpa [List.drop_drop, Nat.succ_mul, Nat.add_comm, List.tail_drop] using next

def rows {O : Type} : Routine Symbol O 32 := Routine.iterate 21 dropRow dropRow_clock

theorem rows_frame {O : Type} (s : Store) (j : Fin 32) (word : j ≠ 2) (buffer : j ≠ 20)
    (rowsClock : j ≠ 21) (clock : j ≠ 22) (scratch : j ≠ 23) : (rows (O := O)).eval s j = s j := by
  exact Routine.iterate_frame 21 (dropRow (O := O)) dropRow_clock j rowsClock
    (fun t => dropRow_frame t j word buffer clock scratch) s

theorem rows_values {O : Type} (s : Store) :
    (rows (O := O)).eval s 2 = (s 2).drop ((s 21).length * (s 27).length) ∧
    (rows (O := O)).eval s 27 = s 27 ∧ (rows (O := O)).eval s 16 = s 16 := by
  have value := iterate_values (O := O) s (s 21).length
  exact ⟨value.1, value.2.1, value.2.2.1⟩

theorem dropRow_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((dropRow (O := O)).eval s) budget ∧ (dropRow (O := O)).cost s ≤ 40 * (budget + 1) := by
  constructor
  · rw [dropRow_eval]
    have dropBound : ((s 2).drop (s 27).length).length ≤ budget := by
      simp only [List.length_drop]
      have bound := sizes 2
      omega
    exact (((sizes.clear 23).clear 22).update 2 _ dropBound).clear 20
  · let a := (Routine.clear (O := O) 20).eval s
    let b := (Routine.assign (O := O) 27 22 23 (by decide) (by decide) (by decide) id).eval a
    let c := (Blocks.routine (O := O) 22 2 20 (by decide) (by decide)).eval b
    have aBound : StoreBound a budget := sizes.clear 20
    have bBound : StoreBound b budget := aBound.assign 27 22 23 (by decide) (by decide) (by decide) id
    have bEmpty : b 20 = [] := by simp [b, a, Routine.assign_eval, Routine.clear]
    have cBound : StoreBound c budget := bBound.block 22 2 20 (by decide) (by decide) (by decide) bEmpty
    have copying : (Routine.assign (O := O) 27 22 23 (by decide) (by decide) (by decide) id).cost a ≤ 20 * budget + 3 := by
      rw [Routine.assign_cost]
      have := aBound 22
      have := aBound 23
      have := aBound 27
      omega
    have blocks := Blocks.routine_cost (O := O) (22 : Fin 32) 2 20 (by decide) (by decide) b
    have source := sizes 20
    have clock := bBound 22
    have erased := cBound 20
    change 3 * (s 20).length + 1 +
      ((Routine.assign (O := O) 27 22 23 (by decide) (by decide) (by decide) id).cost a + 1 +
        ((Blocks.routine (O := O) 22 2 20 (by decide) (by decide)).cost b + 1 + 3 * (c 20).length)) ≤ _
    omega

theorem iterate_bound {O : Type} (s : Store) (budget count : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((counted (O := O)).eval^[count] s) budget := by
  induction count with
  | zero => exact sizes
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      change StoreBound ((dropRow (O := O)).eval
        ((Local.pop (S := Symbol) (21 : Fin 32)).eval ((counted (O := O)).eval^[count] s))) budget
      apply (dropRow_bound (O := O) _ budget _).1
      apply ih.update 21
      change (((counted (O := O)).eval^[count] s) 21).tail.length ≤ budget
      have h := ih 21
      simp only [List.length_tail]
      omega

theorem rows_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((rows (O := O)).eval s) budget ∧
      (rows (O := O)).cost s ≤ (s 21).length * (50 * (budget + 1)) := by
  constructor
  · exact iterate_bound s budget (s 21).length sizes
  · have loop := Routine.loopCost_bound (counted (O := O)).cost (counted (O := O)).eval
      (s 21).length (40 * (budget + 1) + 2) s (by
        intro i inside
        let current := (counted (O := O)).eval^[i] s
        have currentBound : StoreBound current budget := iterate_bound s budget i sizes
        have poppedBound : StoreBound ((Local.pop (S := Symbol) (21 : Fin 32)).eval current) budget :=
          currentBound.update 21 _ (by
            change (current 21).tail.length ≤ budget
            have h := currentBound 21
            simp only [List.length_tail]
            omega)
        have cost := (dropRow_bound (O := O) _ budget poppedBound).2
        change 1 + 1 + (dropRow (O := O)).cost ((Local.pop (S := Symbol) (21 : Fin 32)).eval current) ≤ _
        omega)
    apply loop.trans
    apply Nat.mul_le_mul_left
    omega

theorem rows_randomFree {O : Type} : Command.RandomFree (rows (O := O)).command := by
  simp [rows, dropRow, Blocks.routine, Blocks.body]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Edge
