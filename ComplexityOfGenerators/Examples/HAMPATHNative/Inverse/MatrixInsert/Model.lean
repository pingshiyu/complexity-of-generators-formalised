import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.Value

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem step_row (size position : ℕ) (row rest incoming outRev : List Symbol)
    (width : row.length = size) :
    step size position ⟨row ++ rest, incoming, outRev⟩ =
      ⟨rest, incoming.tail,
        (InsertAt.insertAt row position (incoming.headD (.bit false))).reverse ++ outRev⟩ := by
  simp [step, ← width]

theorem iterate_rows (size position : ℕ) (rows : List (List Symbol))
    (rectangle : ∀ row ∈ rows, row.length = size) (tail incoming outRev : List Symbol) :
    (step size position)^[rows.length] ⟨rows.flatten ++ tail, incoming, outRev⟩ =
      ⟨tail, incoming.drop rows.length, (columns position rows incoming).flatten.reverse ++ outRev⟩ := by
  induction rows generalizing incoming outRev with
  | nil => simp [columns]
  | cons row rest ih =>
      have width := rectangle row (by simp)
      have remaining : ∀ r ∈ rest, r.length = size := by
        intro r member
        exact rectangle r (by simp [member])
      rw [List.length_cons, Function.iterate_succ_apply, List.flatten_cons,
        List.append_assoc, step_row size position row _ incoming outRev width, ih remaining]
      simp [columns, List.reverse_append, List.append_assoc, List.drop_tail]

theorem columns_append (position : ℕ) (first rest : List (List Symbol)) (incoming : List Symbol) :
    columns position (first ++ rest) incoming = columns position first incoming ++
      columns position rest (incoming.drop first.length) := by
  induction first generalizing incoming with
  | nil => simp [columns]
  | cons row first ih => simp [columns, ih, List.drop_tail]

theorem columns_insert (column position : ℕ) (rows : List (List Symbol))
    (fits : position ≤ rows.length) (incoming newRow : List Symbol) :
    columns column (rows.take position) incoming ++ [newRow] ++
        columns column (rows.drop position) (incoming.drop position) =
      (columns column rows incoming).insertIdx position newRow := by
  induction rows generalizing position incoming with
  | nil =>
      have zero : position = 0 := by simpa using fits
      subst position
      rfl
  | cons row rest ih =>
      cases position with
      | zero => rfl
      | succ position =>
          simpa [columns, List.drop_tail] using
            congrArg (InsertAt.insertAt row column (incoming.headD (.bit false)) :: ·)
              (ih position (by simp only [List.length_cons] at fits; omega) incoming.tail)

theorem columns_indexed (size position : ℕ) (rows : List (List Symbol))
    (rectangle : ∀ row ∈ rows, row.length = size) (fits : position ≤ size)
    (incoming : ℕ → Symbol) (offset : ℕ) :
    columns position rows ((List.range' offset rows.length).map incoming) =
      rows.mapIdx (fun index row => row.insertIdx position (incoming (offset+index))) := by
  induction rows generalizing offset with
  | nil => simp [columns]
  | cons row rest ih =>
      have width := rectangle row (by simp)
      have remaining : ∀ r ∈ rest, r.length = size := by
        intro r member
        exact rectangle r (by simp [member])
      simp only [List.length_cons, List.range'_succ, List.map_cons, columns, List.headD_cons,
        List.tail_cons, List.mapIdx_cons]
      rw [InsertAt.insertAt_eq_insertIdx row position _ (by omega), ih remaining]
      simp [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

theorem value_rows (size position : ℕ) (rows : List (List Symbol))
    (count : rows.length = size) (rectangle : ∀ row ∈ rows, row.length = size)
    (fits : position ≤ size) (tail incoming newRow outRev : List Symbol) :
    value size position newRow ⟨rows.flatten ++ tail, incoming, outRev⟩ =
      ⟨tail, incoming.drop size,
        ((columns position (rows.take position) incoming ++ [newRow] ++
          columns position (rows.drop position) (incoming.drop position)).flatten).reverse ++ outRev⟩ := by
  have prefixCount : (rows.take position).length = position := by simp [count, fits]
  have suffixCount : (rows.drop position).length = size-position := by simp [count]
  have prefixRectangle : ∀ row ∈ rows.take position, row.length = size := by
    intro row member
    exact rectangle row (List.mem_of_mem_take member)
  have suffixRectangle : ∀ row ∈ rows.drop position, row.length = size := by
    intro row member
    exact rectangle row (List.mem_of_mem_drop member)
  have splitRows : rows.flatten ++ tail =
      (rows.take position).flatten ++ ((rows.drop position).flatten ++ tail) := by
    rw [← List.append_assoc, ← List.flatten_append, List.take_append_drop]
  unfold value
  rw [splitRows]
  have first := iterate_rows size position (rows.take position) prefixRectangle
    ((rows.drop position).flatten ++ tail) incoming outRev
  rw [prefixCount] at first
  rw [first]
  dsimp only
  have second := iterate_rows size position (rows.drop position) suffixRectangle tail
    (incoming.drop position)
    (newRow.reverse ++ ((columns position (rows.take position) incoming).flatten.reverse ++ outRev))
  rw [suffixCount] at second
  rw [second]
  simp [suffixCount, List.flatten_append, List.reverse_append, List.append_assoc,
    List.drop_drop, Nat.add_sub_of_le fits]

theorem step_measure (size position : ℕ) (state : State) :
    (step size position state).word.length + (step size position state).outRev.length ≤
      state.word.length + state.outRev.length + 1 := by
  simp only [step, List.length_drop, List.length_append, List.length_reverse, InsertAt.insertAt_length]
  simp only [List.length_take]
  omega

theorem iterate_measure (size position count : ℕ) (state : State) :
    ((step size position)^[count] state).word.length +
      ((step size position)^[count] state).outRev.length ≤
        state.word.length + state.outRev.length + count := by
  induction count with
  | zero => simp
  | succ count ih =>
      rw [Function.iterate_succ_apply']
      have next := step_measure size position ((step size position)^[count] state)
      omega

theorem value_graph (graph : Graph) (position : ℕ) (fits : position ≤ graph.size)
    (incoming outgoing : ℕ → Bool) (tail outRev : List Symbol) :
    value graph.size position
      (((List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))).insertIdx
        position (.bit false))
      ⟨graph.matrixWord ++ tail,
        (List.range graph.size).map (fun vertex => Symbol.bit (incoming vertex)), outRev⟩ =
      ⟨tail, [], (graph.insert position incoming outgoing).matrixWord.reverse ++ outRev⟩ := by
  rw [← graphSymbolRows_flatten graph, value_rows graph.size position (graphSymbolRows graph)
    (graphSymbolRows_length graph) (graphSymbolRows_rectangular graph) fits]
  rw [columns_insert position position (graphSymbolRows graph) (by simpa using fits)]
  have indexed := columns_indexed graph.size position (graphSymbolRows graph)
    (graphSymbolRows_rectangular graph) fits (fun vertex => Symbol.bit (incoming vertex)) 0
  simp only [graphSymbolRows_length, List.range'_eq_map_range, List.map_map,
    Function.comp_def, Nat.zero_add] at indexed
  rw [indexed, matrixWord_insert graph position fits]
  simp [insertedSymbolRows, insertMatrixRows]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert
