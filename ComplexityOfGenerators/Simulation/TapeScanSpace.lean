import ComplexityOfGenerators.Simulation.WorkSteps
import ComplexityOfGenerators.Foundations.ExecutionRegions

/-! Native scans with explicit paths and visited-region bounds. These bounds
depend on the scanned coordinates, rather than elapsed running time. -/

namespace ComplexityOfGenerators.Simulation

variable {I A O : Type} (M : Machine I A O)

theorem tapeScan_inRegion (data : InputData I A) (bits : BitString)
    (start : Configuration M) (state : Fin M.states)
    (position : ℕ → ℤ) (direction : ℕ → Move) (steps r : ℕ)
    (bounds : ReadHeadBounds M data start) (region : M.InRegion r start)
    (positions : ∀ j ≤ steps, -(r : ℤ) ≤ position j ∧ position j ≤ r)
    (initialState : start.state = state) (initialHead : start.workHead = position 0)
    (move : ∀ j, j < steps → (direction j).onInt (position j) = position (j + 1))
    (table : ∀ j, j < steps → ∀ input auxiliary index,
      M.transition state input auxiliary index (start.work (position j)) =
        .step state none (direction j) .stay .stay .stay none) :
    ∃ ready, ScanResult M start ready (position steps) ∧
      M.Steps data bits start steps ready ∧ M.InRegion r ready := by
  obtain ⟨ready, scan, path, visited⟩ := tapeScan_path M data bits start state position direction
    steps bounds initialState initialHead move table
  exact ⟨ready, scan, path, visited r region positions⟩

theorem workStep_path (data : InputData I A) (bits : BitString) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols)) (move : Move)
    (table : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) =
        .step state write move .stay .stay .stay none) :
    M.Steps data bits c 1 (workStep M data c state write move) :=
  Machine.Steps.tail .refl (M.next_step _ _ _ _ _ _ _ _ _ _ table)

end ComplexityOfGenerators.Simulation
