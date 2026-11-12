import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixErase.Value
import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixDeleteCodec

/-! The row loop implements deletion on actual word prefixes. The generic
invariant allows both a pending row deletion and an already deleted row. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase

set_option backward.isDefEq.respectTransparency false

theorem step_row (size start : ℕ) (row rest : List Symbol) (width : row.length = size)
    (countdown : ℕ) (pending : Bool) (outRev : List Symbol) :
    step size start ⟨row ++ rest, countdown, pending, outRev⟩ =
      ⟨rest, countdown - 1, if countdown = 0 then false else pending,
        if countdown = 0 ∧ pending = true then outRev else (row.eraseIdx start).reverse ++ outRev⟩ := by
  simp [step, ← width]

/-- A rectangular block scan deletes the selected row once, deletes the same
column in each retained row, and leaves the following word unread. -/
theorem iterate_rows (size start : ℕ) (rows : List (List Symbol))
    (rectangle : ∀ row ∈ rows, row.length = size) (tail : List Symbol)
    (countdown : ℕ) (pending : Bool) (outRev : List Symbol) :
    (step size start)^[rows.length] ⟨rows.flatten ++ tail, countdown, pending, outRev⟩ =
      ⟨tail, countdown - rows.length, pending && decide (rows.length ≤ countdown),
        ((if pending then rows.eraseIdx countdown else rows).map (fun row => row.eraseIdx start)).flatten.reverse ++ outRev⟩ := by
  induction rows generalizing countdown pending outRev with
  | nil => simp
  | cons row rest ih =>
      have width := rectangle row (by simp)
      have remaining : ∀ r ∈ rest, r.length = size := by
        intro r member
        exact rectangle r (by simp [member])
      rw [List.length_cons, Function.iterate_succ_apply, List.flatten_cons,
        List.append_assoc, step_row size start row _ width]
      rw [ih remaining]
      cases countdown with
      | zero => cases pending <;>
          simp [List.flatten_cons, List.reverse_append, List.append_assoc]
      | succ countdown => cases pending <;>
          simp [List.flatten_cons, List.reverse_append, List.append_assoc,
            Nat.succ_sub_succ_eq_sub, Nat.succ_le_succ_iff]

theorem iterate_rows_delete (size start : ℕ) (rows : List (List Symbol))
    (rectangle : ∀ row ∈ rows, row.length = size) (tail : List Symbol) :
    ((step size start)^[rows.length] ⟨rows.flatten ++ tail, start, true, []⟩).word = tail ∧
      ((step size start)^[rows.length] ⟨rows.flatten ++ tail, start, true, []⟩).outRev =
        ((rows.eraseIdx start).map (fun row => row.eraseIdx start)).flatten.reverse := by
  rw [iterate_rows size start rows rectangle tail start true []]
  simp

/-- A row operation consumes at least the bytes that it adds to the output. -/
theorem step_measure (size start : ℕ) (state : State) :
    (step size start state).word.length + (step size start state).outRev.length ≤
      state.word.length + state.outRev.length := by
  have erased := List.length_eraseIdx_le (state.word.take size) start
  simp only [List.length_take] at erased
  dsimp only [step]
  split_ifs <;>
    simp only [List.length_drop, List.length_append, List.length_reverse] <;> omega

theorem step_countdown (size start : ℕ) (state : State) :
    (step size start state).countdown ≤ state.countdown := by
  simp [step]

theorem iterate_countdown (size start count : ℕ) (state : State) :
    ((step size start)^[count] state).countdown = state.countdown - count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      change ((step size start)^[count] state).countdown - 1 = _
      rw [ih]
      omega

theorem iterate_measure (size start count : ℕ) (state : State) :
    ((step size start)^[count] state).word.length +
      ((step size start)^[count] state).outRev.length ≤ state.word.length + state.outRev.length := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      exact (step_measure size start _).trans ih

theorem iterate_word_length_le (size start count : ℕ) (state : State) :
    ((step size start)^[count] state).word.length ≤ state.word.length + state.outRev.length := by
  have bound := iterate_measure size start count state
  omega

theorem iterate_outRev_length_le (size start count : ℕ) (state : State) :
    ((step size start)^[count] state).outRev.length ≤ state.word.length + state.outRev.length := by
  have bound := iterate_measure size start count state
  omega

/-- Canonical graph words instantiate the row invariant without any parsing
or re-encoding assumption on the native controller. -/
theorem iterate_graph (graph : Graph) (start : ℕ) (inside : start < graph.size)
    (tail initialRev : List Symbol) :
    ((step graph.size start)^[graph.size] ⟨graph.matrixWord ++ tail, start, true, initialRev⟩).word = tail ∧
      ((step graph.size start)^[graph.size] ⟨graph.matrixWord ++ tail, start, true, initialRev⟩).outRev =
        (graph.delete start).matrixWord.reverse ++ initialRev := by
  have rows := iterate_rows graph.size start (graphSymbolRows graph)
    (graphSymbolRows_rectangular graph) tail start true initialRev
  rw [graphSymbolRows_length, graphSymbolRows_flatten] at rows
  rw [rows]
  simp only [ite_true, matrixWord_delete_symbol_rows graph start inside, and_self]

end ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase
