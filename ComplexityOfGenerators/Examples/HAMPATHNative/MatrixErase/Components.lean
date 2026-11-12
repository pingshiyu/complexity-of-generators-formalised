import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixErase.Value
import ComplexityOfGenerators.Examples.HAMPATHNative.Cell
import ComplexityOfGenerators.Simulation.WordStack.DropAt

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def columnSlots : DropAt.Layout 32 := ⟨![31, 26, 30, 3, 9], by decide⟩

def encoded (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update (Function.update base
      2 state.word) 3 []) 5 clock) 7 (List.replicate state.countdown (.bit true))) 9 []) 10 [])
      13 (flag state.pending)) 26 (List.replicate start (.bit true))) 27 (List.replicate size (.bit true)))
      29 state.outRev) 30 []) 31 []

def rowPrepare {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [30, 31]).seq
    ((Routine.assign 27 10 9 (by decide) (by decide) (by decide) id).seq
      ((Blocks.routine 10 2 30 (by decide) (by decide)).seq
        ((Routine.transfer 30 31 (by decide) id).seq (DropAt.routine columnSlots (.bit true)))))

def prepared (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) : Store :=
  Function.update (encoded base size start {state with word := state.word.drop size} clock)
    31 ((state.word.take size).eraseIdx start)

theorem rowPrepare_eval {O : Type} (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) :
    (rowPrepare (O := O)).eval (encoded base size start state clock) = prepared base size start state clock := by
  funext j
  fin_cases j <;> simp [rowPrepare, prepared, encoded, columnSlots, Routine.seq, Routine.clearMany_eval,
    Routine.assign_eval, Blocks.routine_eval, Routine.transfer, DropAt.routine_eval]

def rowChoose {O : Type} : Routine Symbol O 32 :=
  Routine.branch 7 fun count => if count.isSome then Routine.transfer 31 29 (by decide) id
  else Routine.branch 13 fun pending => if pending.isSome then Routine.clear 31
    else Routine.transfer 31 29 (by decide) id

def advance : Local Symbol 32 :=
  .read 7 fun count => if count.isSome then Local.pop 7 else Local.pop 13

def rowRoutine {O : Type} : Routine Symbol O 32 :=
  rowPrepare.seq (rowChoose.seq (Routine.ofLocal advance))

def chosen (size start : ℕ) (state : State) : State :=
  ⟨state.word.drop size, state.countdown, state.pending,
    if state.countdown = 0 ∧ state.pending = true then state.outRev
      else ((state.word.take size).eraseIdx start).reverse ++ state.outRev⟩

theorem rowChoose_eval {O : Type} (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) :
    (rowChoose (O := O)).eval (prepared base size start state clock) =
      encoded base size start (chosen size start state) clock := by
  obtain ⟨word, countdown, pending, outRev⟩ := state
  cases countdown <;> cases pending <;> funext j <;>
    by_cases out : j = 29 <;> by_cases temporary : j = 31 <;>
    simp [rowChoose, Routine.branch, Routine.transfer, Routine.clear, prepared, encoded,
      chosen, flag, Function.update_apply, out, temporary, List.replicate_succ]

theorem advance_eval (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) :
    advance.eval (encoded base size start (chosen size start state) clock) =
      encoded base size start (step size start state) clock := by
  obtain ⟨word, countdown, pending, outRev⟩ := state
  cases countdown <;> cases pending <;> funext j <;>
    by_cases count : j = 7 <;> by_cases phase : j = 13 <;>
    simp [advance, Local.eval, Local.pop, Action.apply, encoded, chosen, step, flag,
      Function.update_apply, count, phase, List.replicate_succ]

theorem rowRoutine_eval {O : Type} (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) :
    (rowRoutine (O := O)).eval (encoded base size start state clock) =
      encoded base size start (step size start state) clock := by
  simp only [rowRoutine, Routine.seq, rowPrepare_eval, rowChoose_eval, Routine.ofLocal, advance_eval]

theorem rowRoutine_clock {O : Type} (s : Store) : (rowRoutine (O := O)).eval s 5 = s 5 := by
  have prepareFrame (t : Store) : (rowPrepare (O := O)).eval t 5 = t 5 := by
    simp [rowPrepare, Routine.seq, Routine.clearMany_eval, Routine.assign_eval,
      Blocks.routine_eval (10 : Fin 32) 2 30 (by decide) (by decide) (by decide), Routine.transfer,
      DropAt.routine_eval, columnSlots]
  have chooseFrame (t : Store) : (rowChoose (O := O)).eval t 5 = t 5 := by
    cases count : t 7 <;> cases pending : t 13 <;>
      simp [rowChoose, Routine.branch, Routine.transfer, Routine.clear, count, pending]
  have advanceFrame (t : Store) : advance.eval t 5 = t 5 := by
    cases count : t 7 <;> simp [advance, Local.eval, Local.pop, Action.apply, count]
  change advance.eval ((rowChoose (O := O)).eval ((rowPrepare (O := O)).eval s)) 5 = s 5
  rw [advanceFrame, chooseFrame, prepareFrame]

def counted {O : Type} : Routine Symbol O 32 := Routine.counted 5 rowRoutine

theorem counted_eval {O : Type} (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) :
    (counted (O := O)).eval (encoded base size start state clock) =
      encoded base size start (step size start state) clock.tail := by
  simp only [counted, Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop]
  rw [show encoded base size start state clock 5 = clock by simp [encoded],
    show Function.update (encoded base size start state clock) 5 clock.tail = encoded base size start state clock.tail by
      funext j; fin_cases j <;> simp [encoded], rowRoutine_eval]

theorem iterate_eval {O : Type} (base : Store) (size start : ℕ) (state : State) (clock : List Symbol) (count : ℕ) :
    (counted (O := O)).eval^[count] (encoded base size start state clock) =
      encoded base size start ((step size start)^[count] state) (clock.drop count) := by
  induction count generalizing state clock with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, counted_eval, ih, Function.iterate_succ_apply, List.drop_tail]

def rows {O : Type} : Routine Symbol O 32 := Routine.iterate 5 rowRoutine rowRoutine_clock

theorem rows_eval {O : Type} (base : Store) (size start : ℕ) (state : State) (count : ℕ) :
    (rows (O := O)).eval (encoded base size start state (List.replicate count (.bit true))) =
      encoded base size start ((step size start)^[count] state) [] := by
  simpa [rows, Routine.iterate, encoded, counted] using
    iterate_eval (O := O) base size start state (List.replicate count (.bit true)) count

end ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase
