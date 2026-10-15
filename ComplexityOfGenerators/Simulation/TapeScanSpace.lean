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
  induction steps with
  | zero => exact ⟨start, ⟨rfl, initialHead, rfl, rfl, rfl, rfl, rfl, rfl⟩, .refl, region⟩
  | succ steps ih =>
      obtain ⟨current, scan, path, visited⟩ := ih
        (fun j hj => positions j (by omega))
        (fun j hj => move j (by omega)) (fun j hj => table j (by omega))
      have action : M.transition current.state data.input[current.inputHead]?
          data.auxiliary[current.auxiliaryHead]?
          (if current.indexHead < data.index then some () else none) (current.work current.workHead) =
          .step state none (direction steps) .stay .stay .stay none := by
        rw [scan.state, initialState, scan.head, scan.memory]
        exact table steps (Nat.lt_succ_self _) _ _ _
      let ready := M.stepConfiguration data current state none (direction steps) .stay .stay .stay none
      refine ⟨ready, ⟨initialState.symm, ?_, scan.memory, scan.random, scan.output, ?_, ?_, ?_⟩,
        path.tail (M.next_step _ _ _ _ _ _ _ _ _ _ action), ?_⟩
      · change (direction steps).onInt current.workHead = _
        rw [scan.head]; exact move steps (Nat.lt_succ_self _)
      · change min current.inputHead data.input.length = start.inputHead
        rw [scan.input, Nat.min_eq_left bounds.input]
      · change min current.auxiliaryHead data.auxiliary.length = start.auxiliaryHead
        rw [scan.auxiliary, Nat.min_eq_left bounds.auxiliary]
      · change min current.indexHead data.index = start.indexHead
        rw [scan.index, Nat.min_eq_left bounds.index]
      · apply visited.step M
        rw [scan.head, move steps (Nat.lt_succ_self _)]
        exact positions (steps + 1) le_rfl

theorem workStep_path (data : InputData I A) (bits : BitString) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols)) (move : Move)
    (table : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) =
        .step state write move .stay .stay .stay none) :
    M.Steps data bits c 1 (workStep M data c state write move) :=
  Machine.Steps.tail .refl (M.next_step _ _ _ _ _ _ _ _ _ _ table)

end ComplexityOfGenerators.Simulation
