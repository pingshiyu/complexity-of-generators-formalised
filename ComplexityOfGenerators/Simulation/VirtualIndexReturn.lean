import ComplexityOfGenerators.Simulation.VirtualIndexFetch

/-! The return trip from the virtual index head executes the saved work/output
action and restores both head markers. Its runtime is the sum of the two scan
distances and four actual phase-changing transitions. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

def indexActionValue (action : IndexAction O M.states M.symbols) (old : Option (Fin M.symbols)) :=
  match action.write with | none => old | some symbol => some symbol

def indexActionOutput (action : IndexAction O M.states M.symbols) (old : List O) :=
  match action.emit with | none => old | some symbol => old ++ [symbol]

theorem index_return (data : InputData Unit Bool) (bits : BitString) (length : ℕ)
    (work : ℤ → Option (Fin M.symbols)) (indexHead : ℕ) (workHead : ℤ)
    (action : IndexAction O M.states M.symbols) (negative : Bool) (distance : ℕ)
    (position : workHead = signedPosition negative distance)
    (start : Configuration (virtualIndexCore M))
    (memory : VirtualIndexMemory M length work (some indexHead) (some workHead) start.work)
    (state : start.state = indexControl M (.returnOrigin action negative))
    (head : start.workHead = (indexHead : ℤ)) :
    ∃ ready : Configuration (virtualIndexCore M),
      ready.state = indexControl M (.source action.next
        (workSideAfter M (virtualIndexCell M length work (some indexHead) (some workHead) workHead)
          negative action.move)) ∧
      ready.workHead = action.move.onInt workHead ∧
      VirtualIndexMemory M length (Function.update work workHead (indexActionValue M action (work workHead)))
        (some indexHead) (some (action.move.onInt workHead)) ready.work ∧
      ready.randomHead = start.randomHead ∧ ready.output = indexActionOutput M action start.output ∧
      (virtualIndexCore M).runFrom data bits start (indexHead + distance + 4) =
        (virtualIndexCore M).observe data bits ready := by
  let N := virtualIndexCore M
  let cell := virtualIndexCell M length work (some indexHead) (some workHead) workHead
  let side := workSideAfter M cell negative action.move
  obtain ⟨origin, originScan, originRun⟩ := index_scan_returnOrigin M data bits start action negative
    indexHead state head (fun i => by rw [memory i]; rfl)
  have originMemory : VirtualIndexMemory M length work (some indexHead) (some workHead) origin.work := by
    rw [originScan.memory]
    exact memory
  let entered := N.stepConfiguration data origin (indexControl M (.returnWork action negative))
    none .stay .stay .stay .stay none
  have enterTable : N.transition origin.state data.input[origin.inputHead]?
      data.auxiliary[origin.auxiliaryHead]?
      (if origin.indexHead < data.index then some () else none) (origin.work origin.workHead) =
      .step (indexControl M (.returnWork action negative)) none .stay .stay .stay .stay none := by
    simp [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
      originScan.state, state, originScan.head, originMemory 0, virtualIndexCell]
  have enterLive := N.observe_step data bits origin _ _ _ _ _ _ _ enterTable
  have enterNext := N.next_step data bits origin _ _ _ _ _ _ _ enterTable
  have enterRun : N.runFrom data bits origin 1 = N.observe data bits entered :=
    N.runFrom_shift data bits origin entered enterLive enterNext 0
  have enteredMemory : VirtualIndexMemory M length work (some indexHead) (some workHead) entered.work :=
    originMemory
  obtain ⟨atWork, workScan, workRun⟩ := index_scan_returnWork M data bits entered action negative distance
    rfl (by simpa [entered, Machine.stepConfiguration, Move.onInt] using originScan.head)
    (fun i => by rw [enteredMemory i]; simp [virtualIndexCell, position, eq_comm])
  have atWorkHead : atWork.workHead = workHead := workScan.head.trans position.symm
  have workMemory : VirtualIndexMemory M length work (some indexHead) (some workHead) atWork.work := by
    rw [workScan.memory]
    exact enteredMemory
  let executing := N.stepConfiguration data atWork (indexControl M (.execute action negative))
    none .stay .stay .stay .stay none
  have executeTable : N.transition atWork.state data.input[atWork.inputHead]?
      data.auxiliary[atWork.auxiliaryHead]?
      (if atWork.indexHead < data.index then some () else none) (atWork.work atWork.workHead) =
      .step (indexControl M (.execute action negative)) none .stay .stay .stay .stay none := by
    simp [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
      workScan.state, entered, Machine.stepConfiguration, atWorkHead, workMemory workHead, virtualIndexCell]
  have executeLive := N.observe_step data bits atWork _ _ _ _ _ _ _ executeTable
  have executeNext := N.next_step data bits atWork _ _ _ _ _ _ _ executeTable
  have executeRun : N.runFrom data bits atWork 1 = N.observe data bits executing :=
    N.runFrom_shift data bits atWork executing executeLive executeNext 0
  have executingHead : executing.workHead = workHead := atWorkHead
  have executingMemory : VirtualIndexMemory M length work (some indexHead) (some workHead) executing.work :=
    workMemory
  let written := N.stepConfiguration data executing (indexControl M (.placeWork action.next side))
    (some (indexWrite M {cell with source := indexActionValue M action (work workHead), workHead := false}))
    action.move .stay .stay .stay action.emit
  have writeTable : N.transition executing.state data.input[executing.inputHead]?
      data.auxiliary[executing.auxiliaryHead]?
      (if executing.indexHead < data.index then some () else none) (executing.work executing.workHead) =
      .step (indexControl M (.placeWork action.next side))
        (some (indexWrite M {cell with source := indexActionValue M action (work workHead), workHead := false}))
        action.move .stay .stay .stay action.emit := by
    simp [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
      executing, Machine.stepConfiguration, Move.onInt, atWorkHead, workMemory workHead,
      side, indexActionValue, cell, virtualIndexCell]
    rfl
  have writeLive := N.observe_step data bits executing _ _ _ _ _ _ _ writeTable
  have writeNext := N.next_step data bits executing _ _ _ _ _ _ _ writeTable
  have writeRun : N.runFrom data bits executing 1 = N.observe data bits written :=
    N.runFrom_shift data bits executing written writeLive writeNext 0
  have writtenHead : written.workHead = action.move.onInt workHead := by
    change action.move.onInt executing.workHead = _
    rw [executingHead]
  have writtenMemory : VirtualIndexMemory M length
      (Function.update work workHead (indexActionValue M action (work workHead))) (some indexHead) none
      written.work := by
    have changed := executingMemory.write_source M workHead (indexActionValue M action (work workHead))
    simpa only [written, Machine.stepConfiguration, executingHead, executingMemory workHead] using changed
  let ready := N.stepConfiguration data written (indexControl M (.source action.next side))
    (some (indexWrite M {indexRead M (written.work written.workHead) with workHead := true}))
    .stay .stay .stay .stay none
  have placeTable : N.transition written.state data.input[written.inputHead]?
      data.auxiliary[written.auxiliaryHead]?
      (if written.indexHead < data.index then some () else none) (written.work written.workHead) =
      .step (indexControl M (.source action.next side))
        (some (indexWrite M {indexRead M (written.work written.workHead) with workHead := true}))
        .stay .stay .stay .stay none := by
    simp only [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, written, Machine.stepConfiguration,
      Equiv.symm_apply_apply, virtualIndexTransition]
  have placeLive := N.observe_step data bits written _ _ _ _ _ _ _ placeTable
  have placeNext := N.next_step data bits written _ _ _ _ _ _ _ placeTable
  have placeRun : N.runFrom data bits written 1 = N.observe data bits ready :=
    N.runFrom_shift data bits written ready placeLive placeNext 0
  refine ⟨ready, rfl, writtenHead, ?_, ?_, ?_, ?_⟩
  · have placed := writtenMemory.place_work M (action.move.onInt workHead)
    simpa only [ready, Machine.stepConfiguration, writtenHead] using placed
  · change atWork.randomHead = start.randomHead
    exact workScan.random.trans originScan.random
  · change indexActionOutput M action atWork.output = indexActionOutput M action start.output
    rw [workScan.output]
    change indexActionOutput M action origin.output = _
    rw [originScan.output]
  · have clock : indexHead + distance + 4 = indexHead + (1 + (distance + (1 + (1 + 1)))) := by omega
    rw [clock, N.runFrom_add data bits start origin indexHead originRun,
      N.runFrom_add data bits origin entered 1 enterRun,
      N.runFrom_add data bits entered atWork distance workRun,
      N.runFrom_add data bits atWork executing 1 executeRun,
      N.runFrom_add data bits executing written 1 writeRun]
    exact placeRun

end

end ComplexityOfGenerators.Simulation
