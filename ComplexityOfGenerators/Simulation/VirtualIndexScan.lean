import ComplexityOfGenerators.Simulation.VirtualIndexMemory
import ComplexityOfGenerators.Simulation.TapeScan

/-! Exact scan lengths in the concrete virtual-index routine. Neither scan
changes a tape cell, emits output, or consumes a random bit. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

abbrev virtualIndexCore : Machine Unit Bool O := (virtualIndexRoutine M).machine

def signedPosition (negative : Bool) (distance : ℕ) : ℤ :=
  if negative then -(distance : ℤ) else (distance : ℤ)

@[simp] theorem signedPosition_zero (negative : Bool) : signedPosition negative 0 = 0 := by
  cases negative <;> rfl

theorem signedPosition_ne_zero (negative : Bool) {distance : ℕ} (positive : 0 < distance) :
    signedPosition negative distance ≠ 0 := by cases negative <;> simp [signedPosition] <;> omega

theorem signedPosition_in (negative : Bool) (distance : ℕ) (positive : 0 < distance) :
    (if negative then Move.right else .left).onInt (signedPosition negative distance) =
      signedPosition negative (distance - 1) := by
  cases negative <;> simp [signedPosition, Move.onInt]
  all_goals omega

theorem signedPosition_out (negative : Bool) (distance : ℕ) :
    (if negative then Move.left else .right).onInt (signedPosition negative distance) =
      signedPosition negative (distance + 1) := by
  cases negative <;> simp [signedPosition, Move.onInt]
  all_goals omega

/-- The start and end of a scan have the same finite phase, tape, output, and
random position. Only the physical work head and visited-cell accounting change. -/
structure IndexScanResult (start ready : Configuration (virtualIndexCore M)) (position : ℤ) : Prop where
  state : ready.state = start.state
  head : ready.workHead = position
  memory : ready.work = start.work
  random : ready.randomHead = start.randomHead
  output : ready.output = start.output

theorem index_scan_toOrigin (data : InputData Unit Bool) (bits : BitString)
    (start : Configuration (virtualIndexCore M)) (q : Fin M.states) (negative : Bool)
    (cached : Option (Fin M.symbols)) (distance : ℕ)
    (state : start.state = indexControl M (.toOrigin q negative cached))
    (head : start.workHead = signedPosition negative distance)
    (origin : ∀ i, (indexRead M (start.work i)).origin = decide (i = 0)) :
    ∃ ready, IndexScanResult M start ready 0 ∧
      (virtualIndexCore M).runFrom data bits start distance =
        (virtualIndexCore M).observe data bits ready := by
  obtain ⟨ready, readyState, readyHead, memory, random, output, execution⟩ :=
    tapeScan (virtualIndexCore M) data bits start (indexControl M (.toOrigin q negative cached))
      (fun k => signedPosition negative (distance - k))
      (fun _ => if negative then .right else .left) distance state (by simpa using head)
      (fun k hk => by
        rw [signedPosition_in negative _ (by omega)]
        congr 1)
      (fun k hk input auxiliary index => by
        have notOrigin := signedPosition_ne_zero negative (show 0 < distance - k by omega)
        simp [virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
          origin, notOrigin])
  exact ⟨ready, ⟨readyState.trans state.symm, by simpa using readyHead, memory, random, output⟩, execution⟩

theorem index_scan_toIndex (data : InputData Unit Bool) (bits : BitString)
    (start : Configuration (virtualIndexCore M)) (q : Fin M.states) (negative : Bool)
    (cached : Option (Fin M.symbols)) (indexHead : ℕ)
    (state : start.state = indexControl M (.toIndex q negative cached))
    (head : start.workHead = 0)
    (marker : ∀ i, (indexRead M (start.work i)).indexHead = decide (i = (indexHead : ℤ))) :
    ∃ ready, IndexScanResult M start ready indexHead ∧
      (virtualIndexCore M).runFrom data bits start indexHead =
        (virtualIndexCore M).observe data bits ready := by
  obtain ⟨ready, readyState, readyHead, memory, random, output, execution⟩ :=
    tapeScan (virtualIndexCore M) data bits start (indexControl M (.toIndex q negative cached))
      (fun k => (k : ℤ)) (fun _ => .right) indexHead state head
      (fun k _ => by simp [Move.onInt])
      (fun k hk input auxiliary index => by
        have different : (k : ℤ) ≠ (indexHead : ℤ) := by omega
        simp [virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
          marker, different])
  exact ⟨ready, ⟨readyState.trans state.symm, readyHead, memory, random, output⟩, execution⟩

theorem index_scan_returnOrigin (data : InputData Unit Bool) (bits : BitString)
    (start : Configuration (virtualIndexCore M)) (action : IndexAction O M.states M.symbols)
    (negative : Bool) (distance : ℕ)
    (state : start.state = indexControl M (.returnOrigin action negative))
    (head : start.workHead = (distance : ℤ))
    (origin : ∀ i, (indexRead M (start.work i)).origin = decide (i = 0)) :
    ∃ ready, IndexScanResult M start ready 0 ∧
      (virtualIndexCore M).runFrom data bits start distance =
        (virtualIndexCore M).observe data bits ready := by
  obtain ⟨ready, readyState, readyHead, memory, random, output, execution⟩ :=
    tapeScan (virtualIndexCore M) data bits start (indexControl M (.returnOrigin action negative))
      (fun k => ((distance - k : ℕ) : ℤ)) (fun _ => .left) distance state (by simpa using head)
      (fun k hk => by simp only [Move.onInt]; omega)
      (fun k hk input auxiliary index => by
        have notOrigin : distance - k ≠ 0 := by omega
        simp [virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
          origin, notOrigin])
  exact ⟨ready, ⟨readyState.trans state.symm, by simpa using readyHead, memory, random, output⟩, execution⟩

theorem index_scan_returnWork (data : InputData Unit Bool) (bits : BitString)
    (start : Configuration (virtualIndexCore M)) (action : IndexAction O M.states M.symbols)
    (negative : Bool) (distance : ℕ)
    (state : start.state = indexControl M (.returnWork action negative))
    (head : start.workHead = 0)
    (marker : ∀ i, (indexRead M (start.work i)).workHead =
      decide (i = signedPosition negative distance)) :
    ∃ ready, IndexScanResult M start ready (signedPosition negative distance) ∧
      (virtualIndexCore M).runFrom data bits start distance =
        (virtualIndexCore M).observe data bits ready := by
  obtain ⟨ready, readyState, readyHead, memory, random, output, execution⟩ :=
    tapeScan (virtualIndexCore M) data bits start (indexControl M (.returnWork action negative))
      (signedPosition negative) (fun _ => if negative then .left else .right) distance state
      (by simpa using head) (fun k _ => signedPosition_out negative k)
      (fun k hk input auxiliary index => by
        have different : signedPosition negative k ≠ signedPosition negative distance := by
          cases negative <;> simp [signedPosition] <;> omega
        simp [virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
          marker, different])
  exact ⟨ready, ⟨readyState.trans state.symm, readyHead, memory, random, output⟩, execution⟩

end

end ComplexityOfGenerators.Simulation
