import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.Components
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.Model

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def setup {O : Type} : Routine Symbol O 16 :=
  (Routine.assign 2 6 14 (by decide) (by decide) (by decide) id).seq
    (Routine.assign 1 7 14 (by decide) (by decide) (by decide) id)

theorem setup_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) :
    (setup (O := O)).eval (encoded base size position newRow state firstClock restClock) =
      encoded base size position newRow state (List.replicate position (.bit true))
        (List.replicate size (.bit true)) := by
  funext j
  fin_cases j <;> simp [setup, Routine.seq, Routine.assign_eval, encoded]

def insertRow {O : Type} : Routine Symbol O 16 := Routine.transfer 4 5 (by decide) id

theorem insertRow_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) :
    (insertRow (O := O)).eval (encoded base size position newRow state firstClock restClock) =
      encoded base size position [] { state with outRev := newRow.reverse ++ state.outRev }
        firstClock restClock := by
  funext j
  fin_cases j <;> simp [insertRow, Routine.transfer, encoded]

/-- Insert the fresh row after scanning the first `position` old rows; every
old row receives its corresponding fresh incoming edge in that column. -/
def routine {O : Type} : Routine Symbol O 16 :=
  setup.seq (firstRows.seq (insertRow.seq restRows))

theorem routine_eval {O : Type} (base : Store) (size position : ℕ) (newRow : List Symbol)
    (state : State) (firstClock restClock : List Symbol) :
    (routine (O := O)).eval (encoded base size position newRow state firstClock restClock) =
      encoded base size position [] (value size position newRow state) [] [] := by
  simp only [routine, Routine.seq, setup_eval, firstRows_eval, insertRow_eval,
    List.drop_replicate]
  rw [restRows_eval]
  rfl

theorem routine_rows {O : Type} (base : Store) (size position : ℕ) (rows : List (List Symbol))
    (count : rows.length = size) (rectangle : ∀ row ∈ rows, row.length = size)
    (fits : position ≤ size) (tail incoming newRow outRev firstClock restClock : List Symbol) :
    (routine (O := O)).eval (encoded base size position newRow
      ⟨rows.flatten ++ tail, incoming, outRev⟩ firstClock restClock) =
      encoded base size position []
        ⟨tail, incoming.drop size,
          ((columns position (rows.take position) incoming ++ [newRow] ++
            columns position (rows.drop position) (incoming.drop position)).flatten).reverse ++ outRev⟩ [] [] := by
  rw [routine_eval, value_rows size position rows count rectangle fits]

theorem routine_graph {O : Type} (base : Store) (graph : Graph) (position : ℕ)
    (fits : position ≤ graph.size) (incoming outgoing : ℕ → Bool)
    (tail outRev firstClock restClock : List Symbol) :
    (routine (O := O)).eval (encoded base graph.size position
      (((List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))).insertIdx position (.bit false))
      ⟨graph.matrixWord ++ tail,
        (List.range graph.size).map (fun vertex => Symbol.bit (incoming vertex)), outRev⟩
      firstClock restClock) =
      encoded base graph.size position []
        ⟨tail, [], (graph.insert position incoming outgoing).matrixWord.reverse ++ outRev⟩ [] [] := by
  rw [routine_eval, value_graph graph position fits]

theorem routine_randomFree {O : Type} : Command.RandomFree (routine (O := O)).command := by
  simp [routine, setup, firstRows, firstBody, restRows, rowRoutine, rowPrepare, insertColumn,
    insertRow, InsertAt.routine, DropAt.setup, Blocks.routine, Blocks.body]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert
