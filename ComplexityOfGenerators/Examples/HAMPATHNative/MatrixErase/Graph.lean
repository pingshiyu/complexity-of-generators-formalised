import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixErase.Bounds
import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixDeleteCodec

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase

open Simulation.WordStack

theorem rows_graph {O : Type} (base : Store) (graph : Graph) (start : ℕ)
    (inside : start < graph.size) (tail initialRev : List Symbol) :
    let initial : State := ⟨graph.matrixWord ++ tail, start, true, initialRev⟩
    let result := (rows (O := O)).eval
      (encoded base graph.size start initial (List.replicate graph.size (.bit true)))
    result 2 = tail ∧ result 29 = (graph.delete start).matrixWord.reverse ++ initialRev := by
  dsimp only
  rw [rows_eval]
  have actual := iterate_graph graph start inside tail initialRev
  constructor
  · simpa [encoded] using actual.1
  · simpa [encoded] using actual.2

/-- Concrete primitive executions of the matrix deletion controller. The
clock includes extraction, column erasure, skipped rows and output copying. -/
theorem rows_graph_runs {O : Type} (base : Store) (graph : Graph) (start : ℕ)
    (inside : start < graph.size) (tail initialRev : List Symbol) (budget : ℕ)
    (baseBound : StoreBound base budget) (sizeBound : graph.size ≤ budget)
    (measure : (graph.matrixWord ++ tail).length + initialRev.length ≤ budget)
    {n : ℕ} (bits : BitString) (memory : Memory Symbol O 32) (index : memory.indexHead ≤ n)
    (prepared : memory.store = encoded base graph.size start
      ⟨graph.matrixWord ++ tail, start, true, initialRev⟩ (List.replicate graph.size (.bit true))) :
    ∃ ticks ≤ graph.size * (200 * (budget + 2)), ∃ final,
      (rows (O := O)).command.Runs n bits memory ticks (.done final) ∧
      final.store 2 = tail ∧ final.store 29 = (graph.delete start).matrixWord.reverse ++ initialRev := by
  obtain ⟨ticks, cost, execution⟩ := (rows (O := O)).runs bits memory index
  have bound := rows_cost (O := O) base graph.size start
    ⟨graph.matrixWord ++ tail, start, true, initialRev⟩ graph.size budget
    baseBound sizeBound (by omega) (by change start ≤ budget; omega) sizeBound measure
  have result := rows_graph (O := O) base graph start inside tail initialRev
  refine ⟨ticks, ?_, _, execution, ?_, ?_⟩
  · exact cost.trans (by simpa only [prepared] using bound)
  · simpa only [prepared] using result.1
  · simpa only [prepared] using result.2

end ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase
