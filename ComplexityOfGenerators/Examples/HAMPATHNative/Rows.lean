import ComplexityOfGenerators.Examples.HAMPATHNative.CellModel
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

structure RowState where
  word : List Symbol
  row : ℕ
  valid : Bool

def rowStep (size : ℕ) (state : RowState) : RowState :=
  let scanned := cellStep^[size] ⟨state.word, state.row, true, state.valid⟩
  ⟨scanned.word, state.row + 1, scanned.valid⟩

def rowEncoded (base : Store) (size : ℕ) (state : RowState) (clock : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (cellEncoded base ⟨state.word, 0, false, state.valid⟩ [])
    4 (List.replicate size (.bit true))) 5 clock) 7 (List.replicate state.row (.bit true))) 9 []) 11 []

def rowPrepare {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 7 3 9 (by decide) (by decide) (by decide) id).seq
    ((Routine.ofLocal (Local.push 8 (.bit true))).seq
      (Routine.assign 4 10 9 (by decide) (by decide) (by decide) id))

def rowFinish {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [3, 8, 9, 10]).seq (Routine.ofLocal (Local.push 7 (.bit true)))

def rowRoutine {O : Type} : Routine Symbol O 32 := rowPrepare.seq (cells.seq rowFinish)

theorem rowPrepare_eval {O : Type} (base : Store) (size : ℕ) (state : RowState) (clock : List Symbol) :
    (rowPrepare (O := O)).eval (rowEncoded base size state clock) =
      cellEncoded (rowEncoded base size state clock)
        ⟨state.word, state.row, true, state.valid⟩ (List.replicate size (.bit true)) := by
  funext j
  fin_cases j <;> simp [rowPrepare, rowEncoded, cellEncoded, flag, Routine.seq, Routine.assign_eval,
    Routine.ofLocal, Local.eval, Local.push, Action.apply]

theorem rowRoutine_eval {O : Type} (base : Store) (size : ℕ) (state : RowState) (clock : List Symbol) :
    (rowRoutine (O := O)).eval (rowEncoded base size state clock) =
      rowEncoded base size (rowStep size state) clock := by
  simp only [rowRoutine, Routine.seq, rowPrepare_eval, cells_eval]
  funext j
  fin_cases j <;> simp [rowFinish, rowEncoded, cellEncoded, rowStep, flag, Routine.seq, Routine.clearMany_eval,
    Routine.ofLocal, Local.eval, Local.push, Action.apply, List.replicate_succ]

theorem cells_frame {O : Type} (j : Fin 32) (word : j ≠ 2) (diagonal : j ≠ 3)
    (valid : j ≠ 6) (pending : j ≠ 8) (clock : j ≠ 10) : (cells (O := O)).Fixes j := by
  apply Routine.Fixes.iterate
  · exact clock
  · exact fun s => cellCode_frame s j word diagonal valid pending

theorem rowRoutine_frame {O : Type} (j : Fin 32) (word : j ≠ 2) (diagonal : j ≠ 3)
    (valid : j ≠ 6) (row : j ≠ 7) (pending : j ≠ 8) (scratch : j ≠ 9) (clock : j ≠ 10) :
    (rowRoutine (O := O)).Fixes j := by
  have first : (rowPrepare (O := O)).Fixes j :=
    (Routine.fixes_assign 7 3 9 (by decide) (by decide) (by decide) id j diagonal scratch).seq
      ((Routine.fixes_push (O := O) 8 j (Symbol.bit true) pending).seq
        (Routine.fixes_assign 4 10 9 (by decide) (by decide) (by decide) id j clock scratch))
  have last : (rowFinish (O := O)).Fixes j := by
    intro s
    simp [rowFinish, Routine.seq, Routine.clearMany_eval, Routine.ofLocal, Local.eval, Local.push,
      Action.apply, word, diagonal, valid, row, pending, scratch, clock]
  exact first.seq ((cells_frame j word diagonal valid pending clock).seq last)

theorem rowRoutine_clock {O : Type} (s : Store) : (rowRoutine (O := O)).eval s 5 = s 5 :=
  rowRoutine_frame 5 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) s

def rowCounted {O : Type} : Routine Symbol O 32 := Routine.counted 5 rowRoutine

theorem rowCounted_eval {O : Type} (base : Store) (size : ℕ) (state : RowState) (clock : List Symbol) :
    (rowCounted (O := O)).eval (rowEncoded base size state clock) =
      rowEncoded base size (rowStep size state) clock.tail := by
  simp only [rowCounted, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop]
  rw [show rowEncoded base size state clock 5 = clock by simp [rowEncoded],
    show Function.update (rowEncoded base size state clock) 5 clock.tail = rowEncoded base size state clock.tail by
      simp [rowEncoded, Function.update_comm (show (5 : Fin 32) ≠ 11 by decide),
        Function.update_comm (show (5 : Fin 32) ≠ 9 by decide),
        Function.update_comm (show (5 : Fin 32) ≠ 7 by decide), Function.update_idem], rowRoutine_eval]

theorem rowIterate_eval {O : Type} (base : Store) (size : ℕ) (state : RowState) (clock : List Symbol) (count : ℕ) :
    (rowCounted (O := O)).eval^[count] (rowEncoded base size state clock) =
      rowEncoded base size ((rowStep size)^[count] state) (clock.drop count) := by
  induction count generalizing state clock with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, rowCounted_eval, ih, Function.iterate_succ_apply, List.drop_tail]

def rows {O : Type} : Routine Symbol O 32 := Routine.iterate 5 rowRoutine rowRoutine_clock

theorem rows_eval {O : Type} (base : Store) (size : ℕ) (state : RowState) (count : ℕ) :
    (rows (O := O)).eval (rowEncoded base size state (List.replicate count (.bit true))) =
      rowEncoded base size ((rowStep size)^[count] state) [] := by
  simpa [rows, Routine.iterate, rowEncoded, rowCounted] using
    rowIterate_eval (O := O) base size state (List.replicate count (.bit true)) count

end ComplexityOfGenerators.Examples.HAMPATH.Native
