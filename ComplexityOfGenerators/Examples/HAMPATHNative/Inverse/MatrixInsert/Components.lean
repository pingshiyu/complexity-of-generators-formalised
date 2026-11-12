import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.Value

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 16

def columnSlots : InsertAt.Layout 16 := ⟨![10, 2, 11, 12, 13], by decide⟩

def encoded (base : Store) (size position : ℕ) (newRow : List Symbol) (state : State)
    (firstClock restClock : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update base
      0 state.word) 1 (List.replicate size (.bit true)))
      2 (List.replicate position (.bit true))) 3 state.incoming) 4 newRow) 5 state.outRev)
      6 firstClock) 7 restClock) 8 []) 9 []) 10 []) 11 []) 12 []) 13 []) 14 []

def rowPrepare {O : Type} : Routine Symbol O 16 :=
  (Routine.clearMany [9, 10]).seq
    ((Routine.assign 1 8 14 (by decide) (by decide) (by decide) id).seq
      ((Blocks.routine 8 0 9 (by decide) (by decide)).seq
        (Routine.transfer 9 10 (by decide) id)))

def prepared (base : Store) (size position : ℕ) (newRow : List Symbol) (state : State)
    (firstClock restClock : List Symbol) : Store :=
  Function.update (encoded base size position newRow { state with word := state.word.drop size }
    firstClock restClock) 10 (state.word.take size)

theorem rowPrepare_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) :
    (rowPrepare (O := O)).eval (encoded base size position newRow state firstClock restClock) =
      prepared base size position newRow state firstClock restClock := by
  funext j
  fin_cases j <;> simp [rowPrepare, prepared, encoded, Routine.seq, Routine.clearMany_eval,
    Routine.assign_eval, Blocks.routine_eval, Routine.transfer]

def insertColumn {O : Type} : Routine Symbol O 16 :=
  Routine.branch 3 fun letter => InsertAt.routine columnSlots (.bit true) (letter.getD (.bit false))

theorem insertColumn_eval {O : Type} (s : Store) :
    (insertColumn (O := O)).eval s =
      (InsertAt.routine (O := O) columnSlots (.bit true) ((s 3).head?.getD (.bit false))).eval s := rfl

theorem insertColumn_cost {O : Type} (s : Store) :
    (insertColumn (O := O)).cost s =
      1+(InsertAt.routine (O := O) columnSlots (.bit true) ((s 3).head?.getD (.bit false))).cost s := rfl

def rowRoutine {O : Type} : Routine Symbol O 16 :=
  rowPrepare.seq (insertColumn.seq
    ((Routine.transfer 10 5 (by decide) id).seq (Routine.ofLocal (Local.pop 3))))

def rowOutput (s : Store) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update (Function.update (Function.update s
      0 ((s 0).drop (s 1).length)) 3 (s 3).tail)
      5 ((InsertAt.insertAt ((s 0).take (s 1).length) (s 2).length
        ((s 3).headD (.bit false))).reverse ++ s 5))
      8 []) 9 []) 10 []) 11 []) 12 []) 13 []) 14 []

theorem rowRoutine_eval_store {O : Type} (s : Store) :
    (rowRoutine (O := O)).eval s = rowOutput s := by
  cases incoming : s 3 <;> funext j <;> fin_cases j <;>
    simp [rowRoutine, rowPrepare, insertColumn, Routine.seq, Routine.clearMany_eval,
      Routine.assign_eval, Blocks.routine_eval, Routine.transfer, Routine.branch,
      InsertAt.routine_eval, columnSlots, Routine.ofLocal, Local.eval_pop,
      rowOutput, incoming]

theorem rowRoutine_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) :
    (rowRoutine (O := O)).eval (encoded base size position newRow state firstClock restClock) =
      encoded base size position newRow (step size position state) firstClock restClock := by
  simp only [rowRoutine, Routine.seq, rowPrepare_eval]
  cases incoming : state.incoming <;> funext j <;>
  fin_cases j <;> simp [insertColumn, Routine.branch, InsertAt.routine_eval, columnSlots,
    prepared, encoded, Routine.seq, Routine.transfer, Routine.ofLocal, Local.eval_pop, step,
    List.headD, Option.getD, incoming]

theorem rowRoutine_clock {O : Type} (s : Store) (j : Fin 16) (first : j = 6 ∨ j = 7) :
    (rowRoutine (O := O)).eval s j = s j := by
  rcases first with rfl | rfl <;>
    simp [rowRoutine, rowPrepare, insertColumn, Routine.seq, Routine.clearMany_eval,
      Routine.assign_eval, Blocks.routine_eval, Routine.transfer, Routine.branch,
      InsertAt.routine_eval, columnSlots, Routine.ofLocal, Local.eval_pop]

def firstBody {O : Type} : Routine Symbol O 16 :=
  rowRoutine.seq (Routine.ofLocal (Local.pop 7))

theorem firstBody_clock {O : Type} (s : Store) : (firstBody (O := O)).eval s 6 = s 6 := by
  simp only [firstBody, Routine.seq, Routine.ofLocal, Local.eval_pop]
  simpa using rowRoutine_clock (O := O) s 6 (Or.inl rfl)

def firstRows {O : Type} : Routine Symbol O 16 := Routine.iterate 6 firstBody firstBody_clock

def restRows {O : Type} : Routine Symbol O 16 :=
  Routine.iterate 7 rowRoutine (fun s => rowRoutine_clock s 7 (Or.inr rfl))

theorem firstCounted_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) :
    (Routine.counted 6 (firstBody (O := O))).eval
        (encoded base size position newRow state firstClock restClock) =
      encoded base size position newRow (step size position state) firstClock.tail restClock.tail := by
  simp only [Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop, firstBody]
  rw [show Function.update (encoded base size position newRow state firstClock restClock) 6
      ((encoded base size position newRow state firstClock restClock) 6).tail =
      encoded base size position newRow state firstClock.tail restClock by
    funext j; fin_cases j <;> simp [encoded], rowRoutine_eval]
  funext j
  fin_cases j <;> simp [encoded]

theorem firstIterate_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) (count : ℕ) :
    (Routine.counted 6 (firstBody (O := O))).eval^[count]
        (encoded base size position newRow state firstClock restClock) =
      encoded base size position newRow ((step size position)^[count] state)
        (firstClock.drop count) (restClock.drop count) := by
  induction count generalizing state firstClock restClock with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, firstCounted_eval, ih,
      Function.iterate_succ_apply, List.drop_tail, List.drop_tail]

theorem firstRows_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (restClock : List Symbol) :
    (firstRows (O := O)).eval
        (encoded base size position newRow state (List.replicate position (.bit true)) restClock) =
      encoded base size position newRow ((step size position)^[position] state) [] (restClock.drop position) := by
  simpa [firstRows, Routine.iterate, encoded] using
    firstIterate_eval (O := O) base size position newRow state
      (List.replicate position (.bit true)) restClock position

theorem restCounted_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) :
    (Routine.counted 7 (rowRoutine (O := O))).eval
        (encoded base size position newRow state firstClock restClock) =
      encoded base size position newRow (step size position state) firstClock restClock.tail := by
  simp only [Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop]
  rw [show Function.update (encoded base size position newRow state firstClock restClock) 7
      ((encoded base size position newRow state firstClock restClock) 7).tail =
      encoded base size position newRow state firstClock restClock.tail by
    funext j; fin_cases j <;> simp [encoded], rowRoutine_eval]

theorem restIterate_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) (count : ℕ) :
    (Routine.counted 7 (rowRoutine (O := O))).eval^[count]
        (encoded base size position newRow state firstClock restClock) =
      encoded base size position newRow ((step size position)^[count] state)
        firstClock (restClock.drop count) := by
  induction count generalizing state restClock with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, restCounted_eval, ih,
      Function.iterate_succ_apply, List.drop_tail]

theorem restRows_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock : List Symbol) (count : ℕ) :
    (restRows (O := O)).eval
        (encoded base size position newRow state firstClock (List.replicate count (.bit true))) =
      encoded base size position newRow ((step size position)^[count] state) firstClock [] := by
  simpa [restRows, Routine.iterate, encoded] using
    restIterate_eval (O := O) base size position newRow state firstClock
      (List.replicate count (.bit true)) count

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert
