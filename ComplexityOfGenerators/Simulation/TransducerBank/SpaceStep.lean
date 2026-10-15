import ComplexityOfGenerators.Simulation.TransducerBank.Scans
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceScans

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

/-- Simulation of one tape-bank instruction, including the return to origin.
The finite side bits implement two-way tapes, including crossing zero. -/
theorem bank_step_inRegion (data : InputData I A) (bits : BitString) (r : ℕ) (source : BankConfiguration O Q S k)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (h : BankReady B source negative start) (bounded : B.Bounded data r source)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O)
    (table : B.instruction data source = .step next write work input auxiliary index emit)
    (region : (bankMachine B).InRegion r start)
    (successorBound : B.Bounded data r (B.advance data source next write work input auxiliary index emit)) :
    ∃ t ready sides, t ≤ 2 * r + 4 ∧
      BankReady B (B.advance data source next write work input auxiliary index emit) sides ready ∧
      (bankMachine B).Steps data bits start t ready ∧ (bankMachine B).InRegion r ready := by
  let M := bankMachine B
  let j := B.select source.state
  let position := source.head j
  let newPosition := work.onInt position
  let side := bankSide (decide (position = 0)) (negative j) work
  let sides := Function.update negative j side
  let advanced := B.advance data source next write work input auxiliary index emit
  have sideCorrect : if side then newPosition ≤ 0 else 0 ≤ newPosition :=
    bankSide_correct position (negative j) work (h.side j)
  obtain ⟨fetched, scan, fetchPath, fetchedRegion⟩ :=
    bank_seek_inRegion B data bits r source negative start h bounded region
  have snap := h.toBankSnapshot.scan B scan
  let cell := bankRead B (fetched.work fetched.workHead)
  let written := some (bankAlphabet {cell with
    symbol := Function.update cell.symbol j write
    marked := Function.update cell.marked j false})
  let moved := M.stepConfiguration data fetched
    (bankControl (.place next sides j)) written work input auxiliary index emit
  have cellEq : cell = bankCell source.tape (fun a => some (source.head a)) position := by
    dsimp [cell]
    rw [scan.head, snap.memory]
  have action : M.transition fetched.state data.input[fetched.inputHead]? data.auxiliary[fetched.auxiliaryHead]?
      (if fetched.indexHead < data.index then some () else none)
      (fetched.work fetched.workHead) =
        .step (bankControl (.place next sides j)) written work input auxiliary index emit := by
    rw [scan.state, h.state]
    dsimp [cell] at cellEq
    simp only [M, bankMachine, Equiv.symm_apply_apply, bankTransition]
    rw [cellEq]
    simp only [bankCell, Option.some.injEq, snap.input, snap.auxiliary, snap.index]
    unfold TapeBank.instruction at table
    rw [table]
    simp [j, sides, side, position, written, cell, cellEq, bankCell]
  have actual : M.transition fetched.state data.input[fetched.inputHead]?
      data.auxiliary[fetched.auxiliaryHead]?
      (if fetched.indexHead < data.index then some () else none)
      (fetched.work fetched.workHead) =
        .step (bankControl (.place next sides j)) written work input auxiliary index emit := by
    exact action
  have movePath : M.Steps data bits fetched 1 moved :=
    Machine.Steps.tail .refl (M.next_step _ _ _ _ _ _ _ _ _ _ actual)
  have advancedBound := successorBound
  have newRadius : newPosition.natAbs ≤ r := by
    simpa [advanced, TapeBank.advance, j, newPosition, position] using advancedBound.head j
  have movedRegion : M.InRegion r moved := by
    apply fetchedRegion.step M
    rw [scan.head]
    exact Machine.coordinate_bounds newRadius
  have movedHead : moved.workHead = newPosition := by
    change work.onInt fetched.workHead = _
    rw [scan.head]
  have cleared : BankMemory B advanced.tape
      (Function.update (fun a => some (source.head a)) j none) moved.work := by
    have clear := snap.memory.write_clear B j position write rfl
    simpa only [advanced, TapeBank.advance, moved, Machine.stepConfiguration,
      written, cell, scan.head] using clear
  let placed := workStep M data moved
    (bankControl (.back next sides (sides j)))
    (some (bankAlphabet {bankRead B (moved.work moved.workHead) with
      marked := Function.update (bankRead B (moved.work moved.workHead)).marked j true})) .stay
  have placePath : M.Steps data bits moved 1 placed := by
    apply workStep_path
    simp [M, moved, Machine.stepConfiguration, bankMachine, bankTransition]
  have placeFrame := workStep_frame M data moved
    (bankControl (.back next sides (sides j)))
    (some (bankAlphabet {bankRead B (moved.work moved.workHead) with
      marked := Function.update (bankRead B (moved.work moved.workHead)).marked j true})) .stay
    ((snap.readHeadBounds B bounded).stepConfiguration _ _ _ _ _ _ _ _ _ _)
  have placedMemory : BankMemory B advanced.tape (fun a => some (advanced.head a)) placed.work := by
    have put := cleared.place B j newPosition (by simp)
    have heads : Function.update (Function.update (fun a => some (source.head a)) j none)
        j (some newPosition) = fun a => some (advanced.head a) := by
      funext a
      by_cases same : a = j <;> simp [advanced, TapeBank.advance, j, same, newPosition, position]
    rw [heads] at put
    simpa only [placed, workStep, Machine.stepConfiguration, movedHead, Move.onInt] using put
  have placedSnap : BankSnapshot B advanced placed := by
    refine ⟨placedMemory, ?_, ?_, ?_, ?_, ?_⟩
    · rw [placeFrame.input]
      change input.onInput data.input.length fetched.inputHead = input.onInput data.input.length source.inputHead
      rw [snap.input]
    · rw [placeFrame.auxiliary]
      simp only [moved, Machine.stepConfiguration, TapeBank.advance, advanced, snap.auxiliary, snap.index]
    · rw [placeFrame.index]
      simp only [moved, Machine.stepConfiguration, TapeBank.advance, advanced, snap.auxiliary, snap.index]
    · exact placeFrame.random.trans snap.random
    · rw [placeFrame.output]
      cases emit <;> simp [moved, Machine.stepConfiguration, advanced, TapeBank.advance, snap.output]
  have placedRegion : M.InRegion r placed := by
    apply movedRegion.step M
    change -(r : ℤ) ≤ moved.workHead ∧ moved.workHead ≤ r
    rw [movedHead]
    exact Machine.coordinate_bounds newRadius
  have newPositionEq := signedPosition_natAbs newPosition side sideCorrect
  have placedHead : placed.workHead = signedPosition side newPosition.natAbs := by
    change moved.workHead = _
    exact movedHead.trans newPositionEq
  obtain ⟨returned, backScan, backPath, returnedRegion⟩ :=
    bank_back_inRegion B data bits placed next sides side newPosition.natAbs r newRadius placedRegion
    (placedSnap.readHeadBounds B advancedBound) (by simp [placed, workStep, Machine.stepConfiguration, sides])
    placedHead (fun i => by rw [placedMemory]; rfl)
  have returnedSnap := placedSnap.scan B backScan
  have returnedMemory := returnedSnap.memory
  unfold BankMemory at returnedMemory
  let ready := workStep M data returned (bankControl (.seek next sides)) none .stay
  have finishPath : M.Steps data bits returned 1 ready := by
    apply workStep_path
    rw [backScan.state]
    simp [M, placed, workStep, Machine.stepConfiguration, bankMachine, bankTransition,
      backScan.head, returnedMemory, bankCell]
  have finishFrame := workStep_frame M data returned
    (bankControl (.seek next sides)) none .stay (returnedSnap.readHeadBounds B advancedBound)
  refine ⟨position.natAbs + (1 + (1 + (newPosition.natAbs + 1))), ready, sides, ?_, ?_, ?_, ?_⟩
  · have oldBound := bounded.head j
    have newBound := advancedBound.head j
    simp only [TapeBank.advance, j, Function.update_self] at newBound
    dsimp [position, newPosition, j] at *
    omega
  · constructor
    · exact ⟨returnedSnap.memory, finishFrame.input.trans returnedSnap.input,
        finishFrame.auxiliary.trans returnedSnap.auxiliary,
        finishFrame.index.trans returnedSnap.index,
        finishFrame.random.trans returnedSnap.random, finishFrame.output.trans returnedSnap.output⟩
    · rfl
    · exact backScan.head
    · intro a
      by_cases same : a = j
      · subst a
        simpa [sides, advanced, TapeBank.advance, j] using sideCorrect
      · simpa [sides, advanced, TapeBank.advance, j, same] using h.side a
  · exact fetchPath.trans M (movePath.trans M (placePath.trans M (backPath.trans M finishPath)))
  · apply returnedRegion.step M
    change -(r : ℤ) ≤ returned.workHead ∧ returned.workHead ≤ r
    rw [backScan.head]
    constructor <;> omega

end
end ComplexityOfGenerators.Simulation.TransducerBank
