import ComplexityOfGenerators.Examples.HAMPATHNative.Delete.Components

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Delete

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def startTail (graph : Graph) (start : ℕ) : List Symbol :=
  Symbol.separator :: (List.range graph.size).map (fun v => Symbol.bit (decide (v = start)))

def matrixBase {O : Type} (s : Store) : Store :=
  (header (O := O)).eval ((Routine.assign (O := O) 24 2 9 (by decide) (by decide) (by decide) id).eval s)

theorem matrixPrepare_eval {O : Type} (s : Store) :
    (matrixPrepare (O := O)).eval s =
      MatrixErase.encoded (matrixBase (O := O) s) (headerSize (s 24)) (s 26).length
        ⟨(headerState (s 24)).word, (s 26).length, true, s 29⟩
        (List.replicate (headerSize (s 24)) (.bit true)) := by
  let b := matrixBase (O := O) s
  have source : b 2 = (headerState (s 24)).word := by
    simp [b, matrixBase, Routine.assign_eval, header_eval, rowEncoded, cellEncoded]
  have size : (b 4).length = headerSize (s 24) := by
    simp [b, matrixBase, Routine.assign_eval, header_eval, rowEncoded, cellEncoded]
  have index : (b 26).length = (s 26).length := by
    simp [b, matrixBase, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  have output : b 29 = s 29 := by
    simp [b, matrixBase, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  have clock : b 5 = List.replicate (headerSize (s 24)) (.bit true) := by
    simp [b, matrixBase, Routine.assign_eval, header_eval, rowEncoded, cellEncoded]
  simp only [matrixPrepare, Routine.seq, matrixSetup_eval]
  change MatrixErase.encoded b (b 4).length (b 26).length ⟨b 2, (b 26).length, true, b 29⟩ (b 5) = _
  rw [source, size, index, output, clock]

theorem matrixPrepare_graph {O : Type} (s : Store) (graph : Graph) (start : ℕ)
    (word : s 24 = graph.encode start) (row : (s 26).length = start) :
    (matrixPrepare (O := O)).eval s =
      MatrixErase.encoded (matrixBase (O := O) s) graph.size start
        ⟨graph.matrixWord ++ startTail graph start, start, true, s 29⟩
        (List.replicate graph.size (.bit true)) := by
  rw [matrixPrepare_eval, word, row, headerSize_encode, headerState_encode]
  rfl

theorem matrix_values {O : Type} (s : Store) (graph : Graph) (start : ℕ) (inside : start < graph.size)
    (word : s 24 = graph.encode start) (row : (s 26).length = start) :
    let result := (MatrixErase.rows (O := O)).eval ((matrixPrepare (O := O)).eval s)
    result 29 = (graph.delete start).matrixWord.reverse ++ s 29 ∧ result 31 = [] ∧
    (result 26).length = start ∧ (result 27).length = graph.size ∧ result 28 = s 28 ∧ result 16 = s 16 := by
  dsimp only
  rw [matrixPrepare_graph s graph start word row, MatrixErase.rows_eval]
  have model := MatrixErase.iterate_graph graph start inside (startTail graph start) (s 29)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [MatrixErase.encoded] using model.2
  · simp [MatrixErase.encoded]
  · simp [MatrixErase.encoded]
  · simp [MatrixErase.encoded]
  · simp [MatrixErase.encoded, matrixBase, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  · simp [MatrixErase.encoded, matrixBase, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]

theorem finish_value {O : Type} (s : Store) (empty : s 31 = []) :
    (finish (O := O)).eval s 31 = (s 29).reverse ++ [Symbol.separator] ++
      (List.range ((s 27).length - 1)).map
        (fun i => Symbol.bit (decide (i = contract (s 26).length (s 28).length))) := by
  let a := (Routine.ofLocal (O := O) (Local.push (29 : Fin 32) Symbol.separator)).eval s
  let b := (contractPrepare (O := O)).eval a
  let c := (OneHot.routine (O := O) markSlots Symbol.bit).eval b
  have values := contractPrepare_value (O := O) a
  have position : (b 3).length = contract (s 26).length (s 28).length := by
    simpa [b, a, Routine.ofLocal, Local.eval, Local.push, Action.apply] using congrArg List.length values.1
  have count : (b 5).length = (s 27).length - 1 := by
    simpa [b, a, Routine.ofLocal, Local.eval, Local.push, Action.apply, List.length_tail] using congrArg List.length values.2.1
  have output : b 29 = Symbol.separator :: s 29 := by
    simpa [b, a, Routine.ofLocal, Local.eval, Local.push, Action.apply] using values.2.2.1
  have bEmpty : b 31 = [] := by
    simpa [b, a, Routine.ofLocal, Local.eval, Local.push, Action.apply, empty] using values.2.2.2
  have cOutput : c 29 =
      ((List.range ((s 27).length - 1)).map
        (fun i => Symbol.bit (decide (i = contract (s 26).length (s 28).length)))).reverse ++
        (Symbol.separator :: s 29) := by
    simp [c, OneHot.routine_eval, OneHot.state, markSlots, count, position, output]
  have cEmpty : c 31 = [] := by
    simpa [c, OneHot.routine_eval, OneHot.state, markSlots] using bEmpty
  change (Routine.transfer (O := O) 29 31 (by decide) id).eval c 31 = _
  simp [Routine.transfer, cOutput, cEmpty, List.reverse_append, List.append_assoc]

theorem routine_graph {O : Type} (s : Store) (graph : Graph) (start next : ℕ) (inside : start < graph.size)
    (word : s 24 = graph.encode start) (row : (s 26).length = start)
    (size : (s 27).length = graph.size) (column : (s 28).length = next) :
    (routine (O := O)).eval s 31 = (graph.delete start).encode (contract start next) := by
  let a := (headerPrefix (O := O)).eval s
  let b := (MatrixErase.rows (O := O)).eval ((matrixPrepare (O := O)).eval a)
  have aWord : a 24 = graph.encode start := by simpa [a, headerPrefix_eval] using word
  have aRow : (a 26).length = start := by simpa [a, headerPrefix_eval] using row
  have aNext : (a 28).length = next := by simpa [a, headerPrefix_eval] using column
  have aOutput : a 29 = prefixWord graph.size := by simp [a, headerPrefix_eval, size]
  have values := matrix_values (O := O) a graph start inside aWord aRow
  have bOutput : b 29 = (graph.delete start).matrixWord.reverse ++ prefixWord graph.size := by
    simpa only [b, aOutput] using values.1
  have bEmpty : b 31 = [] := values.2.1
  have bRow : (b 26).length = start := values.2.2.1
  have bSize : (b 27).length = graph.size := values.2.2.2.1
  have bNext : (b 28).length = next := by rw [show b 28 = a 28 from values.2.2.2.2.1, aNext]
  change (finish (O := O)).eval b 31 = _
  rw [finish_value b bEmpty, bOutput, bRow, bSize, bNext]
  have encoding (g : Graph) (v : ℕ) : g.encode v = List.replicate g.size (.bit true) ++ [Symbol.separator] ++
      g.matrixWord ++ [Symbol.separator] ++ (List.range g.size).map (fun i => Symbol.bit (decide (i = v))) := rfl
  have childSize : (graph.delete start).size = graph.size - 1 := rfl
  rw [encoding, childSize]
  simp [prefixWord, List.reverse_append, List.append_assoc]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Delete
