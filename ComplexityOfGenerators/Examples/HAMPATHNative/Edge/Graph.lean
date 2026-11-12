import ComplexityOfGenerators.Examples.HAMPATHNative.Edge.Basic
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Edge

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem bitAt_graph (s : Store) (graph : Graph) (start next : ℕ)
    (startBound : start < graph.size) (nextBound : next < graph.size)
    (word : s 24 = graph.encode start) (row : (s 26).length = start)
    (size : (s 27).length = graph.size) (column : (s 28).length = next) :
    bitAt s = some (.bit (graph.edge start next)) := by
  rw [bitAt, word, row, size, column, headerState_encode]
  have inside : start * graph.size + next < graph.matrixWord.length := by
    rw [Graph.matrixWord_length]
    nlinarith only [startBound, nextBound, Nat.zero_le next, Nat.zero_le start,
      Nat.zero_le graph.size, Nat.mul_le_mul_right graph.size (by omega : start + 1 ≤ graph.size)]
  simp only [List.head?_eq_getElem?, List.getElem?_drop, Nat.add_zero]
  rw [List.getElem?_append_left inside]
  exact graph.matrixWord_lookup start next startBound nextBound

theorem query_graph_flag {O : Type} (s : Store) (graph : Graph) (start next : ℕ)
    (startBound : start < graph.size) (nextBound : next < graph.size)
    (word : s 24 = graph.encode start) (row : (s 26).length = start)
    (size : (s 27).length = graph.size) (column : (s 28).length = next) :
    (query (O := O)).eval s 16 = if graph.edge start next then s 16 else [] := by
  rw [query_flag, bitAt_graph s graph start next startBound nextBound word row size column]
  cases graph.edge start next <;> simp

theorem query_frame {O : Type} (s : Store) (j : Fin 32) (outside : 24 ≤ j.val) :
    (query (O := O)).eval s j = s j := by
  have prepareFrame (t : Store) : (prepare (O := O)).eval t j = t j := by
    fin_cases j <;> norm_num at outside <;>
      simp [prepare, Routine.seq, Routine.assign_eval, header_eval, rowEncoded, cellEncoded, headerBase]
  have rowFrame (t : Store) : (rows (O := O)).eval t j = t j :=
    rows_frame t j (by omega) (by omega) (by omega) (by omega) (by omega)
  have columnFrame (t : Store) : (column (O := O)).eval t j = t j := by
    have word : j ≠ 2 := by omega
    have buffer : j ≠ 20 := by omega
    have clock : j ≠ 22 := by omega
    have scratch : j ≠ 23 := by omega
    simp [column_eval, word, buffer, clock, scratch]
  have headFrame (t : Store) : (headCheck (O := O)).eval t j = t j := by
    have valid : j ≠ 16 := by omega
    simp [headCheck_eval, valid]
  simp only [query, Routine.seq]
  rw [headFrame, columnFrame, rowFrame, prepareFrame]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Edge
