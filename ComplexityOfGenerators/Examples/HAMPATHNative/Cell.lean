import ComplexityOfGenerators.Examples.HAMPATHParser
import ComplexityOfGenerators.Simulation.WordStack.RandomFree
import Mathlib.Tactic.FinCases

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 32

def flag (value : Bool) : List Symbol := if value then [.bit true] else []

structure CellState where
  word : List Symbol
  diagonal : ℕ
  pending : Bool
  valid : Bool

def cellStep (state : CellState) : CellState :=
  let allowed := match state.word with
    | .bit value :: _ => !(value && decide (state.diagonal = 0) && state.pending)
    | _ => false
  ⟨state.word.tail, state.diagonal - 1,
    if state.diagonal = 0 then false else state.pending, state.valid && allowed⟩

/-- The only distinguished matrix cell in a row is its diagonal. A unary
countdown locates that cell without a comparison subroutine. -/
def cellCode : Local Symbol 32 :=
  (Local.read 2 fun head => match head with
    | some (.bit false) => .skip
    | some (.bit true) => Local.read 3 fun count =>
        if count.isSome then .skip else Local.read 8 fun pending =>
          if pending.isSome then Local.pop 6 else .skip
    | _ => Local.pop 6).seq
  ((Local.read 3 fun count => if count.isSome then Local.pop 3 else Local.pop 8).seq (Local.pop 2))

def cellEncoded (base : Store) (state : CellState) (clock : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update base
    2 state.word) 3 (List.replicate state.diagonal (.bit true)))
    6 (flag state.valid)) 8 (flag state.pending)) 10 clock

theorem cellCode_frame (s : Store) (j : Fin 32) (word : j ≠ 2) (diagonal : j ≠ 3)
    (valid : j ≠ 6) (pending : j ≠ 8) : cellCode.eval s j = s j := by
  cases count : s 3 <;> cases phase : s 8 <;> cases head : (s 2).head? with
  | none => simp [cellCode, Local.eval, Local.pop, Action.apply, head, count, phase, word, diagonal, valid, pending]
  | some symbol => cases symbol with
    | separator => simp [cellCode, Local.eval, Local.pop, Action.apply, head, count, phase, word, diagonal, valid, pending]
    | bit value => cases value <;> simp [cellCode, Local.eval, Local.pop, Action.apply, head, count, phase,
        word, diagonal, valid, pending]

theorem cellCode_eval (base : Store) (state : CellState) (clock : List Symbol) :
    cellCode.eval (cellEncoded base state clock) = cellEncoded base (cellStep state) clock := by
  funext j
  by_cases owned : j = 2 ∨ j = 3 ∨ j = 6 ∨ j = 8
  · obtain ⟨word, diagonal, pending, valid⟩ := state
    rcases owned with rfl | rfl | rfl | rfl <;>
      cases diagonal <;> cases pending <;> cases valid <;>
      cases word with
      | nil => simp [cellCode, cellEncoded, cellStep, flag, Local.eval, Local.pop, Action.apply]
      | cons head rest => cases head with
        | separator => simp [cellCode, cellEncoded, cellStep, flag, Local.eval, Local.pop, Action.apply,
            List.replicate_succ]
        | bit value => cases value <;> simp [cellCode, cellEncoded, cellStep, flag, Local.eval, Local.pop,
            Action.apply, List.replicate_succ]
  · have word : j ≠ 2 := fun equal => owned (Or.inl equal)
    have diagonal : j ≠ 3 := fun equal => owned (Or.inr (Or.inl equal))
    have valid : j ≠ 6 := fun equal => owned (Or.inr (Or.inr (Or.inl equal)))
    have pending : j ≠ 8 := fun equal => owned (Or.inr (Or.inr (Or.inr equal)))
    rw [cellCode_frame _ j word diagonal valid pending]
    simp [cellEncoded, Function.update_apply, word, diagonal, valid, pending]

theorem cellCode_clock (s : Store) : cellCode.eval s 10 = s 10 :=
  cellCode_frame s 10 (by decide) (by decide) (by decide) (by decide)

theorem cellCode_ticks (s : Store) : cellCode.ticks s ≤ 12 := by
  cases count : s 3 <;> cases phase : s 8 <;> cases head : (s 2).head? with
  | none => simp [cellCode, Local.ticks, Local.eval, Local.pop, Action.apply, head, count, phase]
  | some symbol => cases symbol with
    | separator => simp [cellCode, Local.ticks, Local.eval, Local.pop, Action.apply, head, count, phase]
    | bit value => cases value <;> simp [cellCode, Local.ticks, Local.eval, Local.pop, Action.apply,
        head, count, phase]

def cellCounted {O : Type} : Routine Symbol O 32 := Routine.counted 10 (Routine.ofLocal cellCode)

theorem cellCounted_eval {O : Type} (base : Store) (state : CellState) (clock : List Symbol) :
    (cellCounted (O := O)).eval (cellEncoded base state clock) =
      cellEncoded base (cellStep state) clock.tail := by
  simp only [cellCounted, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop]
  rw [show cellEncoded base state clock 10 = clock by simp [cellEncoded],
    show Function.update (cellEncoded base state clock) 10 clock.tail = cellEncoded base state clock.tail by
      simp [cellEncoded, Function.update_idem], cellCode_eval]

theorem cellIterate_eval {O : Type} (base : Store) (state : CellState) (clock : List Symbol) (count : ℕ) :
    (cellCounted (O := O)).eval^[count] (cellEncoded base state clock) =
      cellEncoded base (cellStep^[count] state) (clock.drop count) := by
  induction count generalizing state clock with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply, cellCounted_eval, ih, Function.iterate_succ_apply, List.drop_tail]

def cells {O : Type} : Routine Symbol O 32 := Routine.iterate 10 (Routine.ofLocal cellCode) cellCode_clock

theorem cells_eval {O : Type} (base : Store) (state : CellState) (count : ℕ) :
    (cells (O := O)).eval (cellEncoded base state (List.replicate count (.bit true))) =
      cellEncoded base (cellStep^[count] state) [] := by
  simpa [cells, Routine.iterate, cellEncoded, cellCounted] using
    cellIterate_eval (O := O) base state (List.replicate count (.bit true)) count

theorem cells_cost {O : Type} (s : Store) : (cells (O := O)).cost s ≤ 16 * (s 10).length := by
  have bounded := Routine.loopCost_bound (cellCounted (O := O)).cost (cellCounted (O := O)).eval
    (s 10).length 14 s (by
      intro i _
      have cost := cellCode_ticks ((Local.pop 10).eval ((cellCounted (O := O)).eval^[i] s))
      change 1 + 1 + cellCode.ticks ((Local.pop 10).eval ((cellCounted (O := O)).eval^[i] s)) ≤ 14
      omega)
  simpa [cells, Routine.iterate, cellCounted, Nat.mul_comm] using bounded

end ComplexityOfGenerators.Examples.HAMPATH.Native
