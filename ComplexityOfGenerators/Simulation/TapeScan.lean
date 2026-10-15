import ComplexityOfGenerators.Foundations.ExecutionRegions

/-!
# Exact runtime of native tape scans

A scan is a sequence of actual finite-control `step` instructions. The proof
keeps the work tape, random position, and output unchanged and counts one native
transition per traversed edge. The final observation may halt; no additional
transition is charged for that observation.
-/

namespace ComplexityOfGenerators.Simulation

variable {I A O : Type} (M : Machine I A O)

/-- The read-only head bounds needed for a `stay` movement to leave a
configuration unchanged. Unlike work heads, these heads are clamped. -/
structure ReadHeadBounds (data : InputData I A) (c : Configuration M) : Prop where
  input : c.inputHead ≤ data.input.length
  auxiliary : c.auxiliaryHead ≤ data.auxiliary.length
  index : c.indexHead ≤ data.index

/-- Everything a pure work-tape scan preserves, including the three physical
read-only heads used by a suspended source instruction. -/
structure ScanResult (start ready : Configuration M) (position : ℤ) : Prop where
  state : ready.state = start.state
  head : ready.workHead = position
  memory : ready.work = start.work
  random : ready.randomHead = start.randomHead
  output : ready.output = start.output
  input : ready.inputHead = start.inputHead
  auxiliary : ready.auxiliaryHead = start.auxiliaryHead
  index : ready.indexHead = start.indexHead

theorem ScanResult.readHeadBounds {data : InputData I A} {start ready : Configuration M}
    {position : ℤ} (h : ScanResult M start ready position) (bound : ReadHeadBounds M data start) :
    ReadHeadBounds M data ready := by
  constructor
  · rw [h.input]; exact bound.input
  · rw [h.auxiliary]; exact bound.auxiliary
  · rw [h.index]; exact bound.index

/-- A scan has one concrete path. Region preservation is conditional on the
initial visited set and the scanned coordinates, independently of runtime. -/
theorem tapeScan_path (data : InputData I A) (bits : BitString)
    (start : Configuration M) (state : Fin M.states)
    (position : ℕ → ℤ) (direction : ℕ → Move) (steps : ℕ)
    (bounds : ReadHeadBounds M data start)
    (initialState : start.state = state) (initialHead : start.workHead = position 0)
    (move : ∀ j, j < steps → (direction j).onInt (position j) = position (j + 1))
    (table : ∀ j, j < steps → ∀ input auxiliary index,
      M.transition state input auxiliary index (start.work (position j)) =
        .step state none (direction j) .stay .stay .stay none) :
    ∃ ready, ScanResult M start ready (position steps) ∧
      M.Steps data bits start steps ready ∧
      ∀ r, M.InRegion r start → (∀ j ≤ steps, -(r : ℤ) ≤ position j ∧ position j ≤ r) →
        M.InRegion r ready := by
  induction steps with
  | zero => exact ⟨start, ⟨rfl, initialHead, rfl, rfl, rfl, rfl, rfl, rfl⟩, .refl, fun _ region _ => region⟩
  | succ steps ih =>
      obtain ⟨current, scan, path, visited⟩ := ih
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
      · intro r region positions
        apply (visited r region (fun j hj => positions j (by omega))).step M
        rw [scan.head, move steps (Nat.lt_succ_self _)]
        exact positions (steps + 1) le_rfl

theorem tapeScan_with_heads (data : InputData I A) (bits : BitString)
    (start : Configuration M) (state : Fin M.states)
    (position : ℕ → ℤ) (direction : ℕ → Move) (steps : ℕ)
    (bounds : ReadHeadBounds M data start)
    (initialState : start.state = state) (initialHead : start.workHead = position 0)
    (move : ∀ k, k < steps → (direction k).onInt (position k) = position (k + 1))
    (table : ∀ k, k < steps → ∀ input auxiliary index,
      M.transition state input auxiliary index (start.work (position k)) =
        .step state none (direction k) .stay .stay .stay none) :
    ∃ ready : Configuration M, ScanResult M start ready (position steps) ∧
      M.runFrom data bits start steps = M.observe data bits ready := by
  obtain ⟨ready, scan, path, _⟩ := tapeScan_path M data bits start state position direction
    steps bounds initialState initialHead move table
  exact ⟨ready, scan, path.runFrom M⟩

theorem tapeScan (data : InputData I A) (bits : BitString)
    (start : Configuration M) (state : Fin M.states)
    (position : ℕ → ℤ) (direction : ℕ → Move) (steps : ℕ)
    (initialState : start.state = state) (initialHead : start.workHead = position 0)
    (move : ∀ k, k < steps → (direction k).onInt (position k) = position (k + 1))
    (table : ∀ k, k < steps → ∀ input auxiliary index,
      M.transition state input auxiliary index (start.work (position k)) =
        .step state none (direction k) .stay .stay .stay none) :
    ∃ ready : Configuration M,
      ready.state = state ∧ ready.workHead = position steps ∧ ready.work = start.work ∧
      ready.randomHead = start.randomHead ∧ ready.output = start.output ∧
      M.runFrom data bits start steps = M.observe data bits ready := by
  induction steps with
  | zero => exact ⟨start, initialState, initialHead, rfl, rfl, rfl, rfl⟩
  | succ steps ih =>
      obtain ⟨current, currentState, currentHead, memory, random, output, execution⟩ :=
        ih (fun k hk => move k (by omega)) (fun k hk => table k (by omega))
      have action : M.transition current.state data.input[current.inputHead]?
          data.auxiliary[current.auxiliaryHead]?
          (if current.indexHead < data.index then some () else none) (current.work current.workHead) =
          .step state none (direction steps) .stay .stay .stay none := by
        rw [currentState, currentHead, memory]
        exact table steps (Nat.lt_succ_self _) _ _ _
      let ready := M.stepConfiguration data current state none (direction steps) .stay .stay .stay none
      have live := M.observe_step data bits current _ _ _ _ _ _ _ action
      have next := M.next_step data bits current _ _ _ _ _ _ _ action
      refine ⟨ready, rfl, ?_, memory, random, output, ?_⟩
      · change (direction steps).onInt current.workHead = _
        rw [currentHead]
        exact move steps (Nat.lt_succ_self _)
      · simp only [Machine.runFrom, execution, live, next]
        rfl

/-- A work scan can simultaneously reset the physical input head. This is
needed because the native read-only tape has no explicit left-end marker. -/
theorem tapeScan_inputLeft (data : InputData I A) (bits : BitString)
    (start : Configuration M) (state : Fin M.states)
    (position : ℕ → ℤ) (direction : ℕ → Move) (steps : ℕ)
    (bounds : ReadHeadBounds M data start)
    (initialState : start.state = state) (initialHead : start.workHead = position 0)
    (move : ∀ k, k < steps → (direction k).onInt (position k) = position (k + 1))
    (table : ∀ k, k < steps → ∀ input auxiliary index,
      M.transition state input auxiliary index (start.work (position k)) =
        .step state none (direction k) .left .stay .stay none) :
    ∃ ready : Configuration M,
      ready.state = state ∧ ready.workHead = position steps ∧ ready.work = start.work ∧
      ready.randomHead = start.randomHead ∧ ready.output = start.output ∧
      ready.inputHead = start.inputHead - steps ∧
      ready.auxiliaryHead = start.auxiliaryHead ∧ ready.indexHead = start.indexHead ∧
      M.runFrom data bits start steps = M.observe data bits ready := by
  induction steps with
  | zero => exact ⟨start, initialState, initialHead, rfl, rfl, rfl, by omega, rfl, rfl, rfl⟩
  | succ steps ih =>
      obtain ⟨current, currentState, currentHead, memory, random, output, input, auxiliary, index, execution⟩ :=
        ih (fun k hk => move k (by omega)) (fun k hk => table k (by omega))
      have action : M.transition current.state data.input[current.inputHead]?
          data.auxiliary[current.auxiliaryHead]?
          (if current.indexHead < data.index then some () else none) (current.work current.workHead) =
          .step state none (direction steps) .left .stay .stay none := by
        rw [currentState, currentHead, memory]
        exact table steps (Nat.lt_succ_self _) _ _ _
      let ready := M.stepConfiguration data current state none (direction steps) .left .stay .stay none
      have live := M.observe_step data bits current _ _ _ _ _ _ _ action
      have next := M.next_step data bits current _ _ _ _ _ _ _ action
      refine ⟨ready, rfl, ?_, memory, random, output, ?_, ?_, ?_, ?_⟩
      · change (direction steps).onInt current.workHead = _
        rw [currentHead]
        exact move steps (Nat.lt_succ_self _)
      · change current.inputHead - 1 = start.inputHead - (steps + 1)
        omega
      · change min current.auxiliaryHead data.auxiliary.length = start.auxiliaryHead
        rw [auxiliary, Nat.min_eq_left bounds.auxiliary]
      · change min current.indexHead data.index = start.indexHead
        rw [index, Nat.min_eq_left bounds.index]
      · simp only [Machine.runFrom, execution, live, next]
        rfl

end ComplexityOfGenerators.Simulation
