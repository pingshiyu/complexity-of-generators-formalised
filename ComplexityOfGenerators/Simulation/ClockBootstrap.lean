import ComplexityOfGenerators.Simulation.ClockLoader

/-! Connecting the verified block loader and input-reset scans to the actual
blank-tape initial configuration of the clocked machine. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I O : Type} [Fintype I] [Fintype O] (M : Machine I Bool O) (p : PolynomialBound)

omit [Fintype O] in
theorem clock_reset_entry (w : List I) (bits : BitString) :
    ∃ ready : Configuration (clockInputReset M p),
      ready.state = (0 : Fin 3) ∧ ready.workHead = 0 ∧ ready.inputHead ≤ w.length ∧
      ready.auxiliaryHead = 0 ∧ ready.indexHead = 0 ∧ ready.randomHead = 0 ∧ ready.output = [] ∧
      PolynomialClockMemory M p (w.length + 1) (fun _ => none)
        (clockLocations (List.replicate p.degree 0)) (some 0) ready.work ∧
      (clockPreparedLoader M p).run (decisionData w) bits (4 * w.length + 10) =
        (clockPreparedLoader M p).observe (decisionData w) bits
          (sequenceRightConfiguration (clockLoader M p) (machineRoutine (clockInputReset M p)) ready) := by
  let L := clockLoader M p
  let routine := machineRoutine (clockInputReset M p)
  let C := clockPreparedLoader M p
  let data := decisionData w
  obtain ⟨marker, markerState, markerHead, markerMemory, _, markerRun⟩ :=
    block_at_marker (clockLoaderProgram M p) (Fintype.equivFin Unit) (clockAlphabet M p) (clockBlocks M p) w bits
  change Configuration L at marker
  have time : 2 * ((clockBlocks M p).word w).length + 2 * w.length + 4 = 4 * w.length + 8 := by simp; omega
  rw [time] at markerRun
  have atMarker : L.run data bits (4 * w.length + 8) = .running marker := markerRun
  have markerRandom := L.deterministic_running_randomHead
    (blockMachine_deterministic (clockLoaderProgram M p) (Fintype.equivFin Unit) (clockAlphabet M p) (clockBlocks M p))
    data bits _ marker atMarker
  have markerRead : marker.work marker.workHead = some (Fin.last (Fintype.card (ClockCell M.symbols p.degree))) := by
    rw [markerHead, markerMemory]
    simp [bootMemory]
  let done := L.stepConfiguration data marker
    (blockControl (clockBlocks M p) (.run ((Fintype.equivFin Unit) ()))) none .right .stay .stay .stay none
  have table : L.transition marker.state data.input[marker.inputHead]? data.auxiliary[marker.auxiliaryHead]?
      (if marker.indexHead < data.index then some () else none) (marker.work marker.workHead) =
      .step (blockControl (clockBlocks M p) (.run ((Fintype.equivFin Unit) ()))) none .right .stay .stay .stay none := by
    simp [L, clockLoader, blockMachine, blockTransition, markerState, markerRead]
  have markerLive := L.observe_step data bits marker _ _ _ _ _ _ _ table
  have markerNext := L.next_step data bits marker _ _ _ _ _ _ _ table
  have accepts : L.transition done.state data.input[done.inputHead]? data.auxiliary[done.auxiliaryHead]?
      (if done.indexHead < data.index then some () else none) (done.work done.workHead) = .accept := by
    simp [L, clockLoader, done, Machine.stepConfiguration, blockMachine, blockTransition, clockLoaderProgram, postInstruction]
  let ready : Configuration (clockInputReset M p) := handoffConfiguration L routine data done []
  have head : ready.workHead = 0 := by
    simp [ready, handoffConfiguration, done, Machine.stepConfiguration, Move.onInt, markerHead]
  have prepared : PolynomialClockMemory M p (w.length + 1) (fun _ => none)
      (clockLocations (List.replicate p.degree 0)) (some 0) ready.work := by
    change PolynomialClockMemory M p _ _ _ _ marker.work
    rw [markerMemory, clockBlocks_word]
    simpa only [List.length_cons, List.length_append, List.length_replicate, List.length_singleton,
      List.length_nil, Nat.zero_add, Nat.add_assoc] using clock_initial_memory M p w.length
  have live := sequence_left_observe L routine data bits marker [] markerLive
  have next := sequence_left_next L routine data bits marker done [] markerNext
  have enterRun : C.runFrom data bits (sequenceLeftConfiguration L routine marker []) 1 =
      C.observe data bits (sequenceLeftConfiguration L routine done []) :=
    C.runFrom_shift data bits _ _ live next 0
  have handoffRun := sequence_accept_handoff L routine data bits done [] accepts
  have loadedPrefix := sequence_left_running L routine data bits L.initialConfiguration marker [] (4 * w.length + 8)
    (by simpa using atMarker)
  have initial : sequenceLeftConfiguration L routine L.initialConfiguration [] = C.initialConfiguration := rfl
  rw [initial] at loadedPrefix
  have prefixRun : C.runFrom data bits C.initialConfiguration (4 * w.length + 8) =
      C.observe data bits (sequenceLeftConfiguration L routine marker []) := loadedPrefix.trans live.symm
  refine ⟨ready, rfl, head, ?_, ?_, ?_, markerRandom, rfl, prepared, ?_⟩
  · exact Nat.min_le_right _ _
  · simp [ready, handoffConfiguration, data, decisionData, Move.onInput]
  · simp [ready, handoffConfiguration, data, decisionData, Move.onInput]
  · have total : 4 * w.length + 10 = (4 * w.length + 8) + (1 + 1) := by omega
    change C.run data bits _ = _
    rw [total, ← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ _ prefixRun,
      C.runFrom_add data bits _ _ 1 enterRun]
    exact handoffRun

omit [Fintype O] in
theorem clock_prepared_loader (w : List I) (bits : BitString) :
    ∃ ready : Configuration (clockPreparedLoader M p),
      ready.workHead = 0 ∧ ready.inputHead = 0 ∧ ready.auxiliaryHead = 0 ∧ ready.indexHead = 0 ∧
      ready.randomHead = 0 ∧ ready.output = [] ∧
      PolynomialClockMemory M p (w.length + 1) (fun _ => none)
        (clockLocations (List.replicate p.degree 0)) (some 0) ready.work ∧
      (clockPreparedLoader M p).transition ready.state w[ready.inputHead]? none none (ready.work ready.workHead) =
        .step (sequenceControl (clockLoader M p) (machineRoutine (clockInputReset M p)) (.inr (2 : Fin 3)))
          none .stay .stay .stay .stay none ∧
      (clockPreparedLoader M p).run (decisionData w) bits (6 * w.length + 13) = .running ready := by
  let L := clockLoader M p
  let routine := machineRoutine (clockInputReset M p)
  let R := clockInputReset M p
  let C := clockPreparedLoader M p
  let data := decisionData w
  obtain ⟨entered, state, head, input, auxiliary, index, random, output, memory, loaded⟩ := clock_reset_entry M p w bits
  have bounds : ReadHeadBounds R data entered := ⟨input, by simp [auxiliary, data, decisionData], by simp [index, data, decisionData]⟩
  obtain ⟨atOrigin, originState, originHead, originInput, originMemory, originRandom, originOutput,
      originAux, originIndex, resetRun⟩ := clock_input_reset M p data bits (w.length + 1) entered bounds (by omega)
        state head (fun i => by rw [memory i]; rfl) (fun i => by rw [memory i]; rfl)
  let ready := sequenceRightConfiguration L routine atOrigin
  have prepared : PolynomialClockMemory M p (w.length + 1) (fun _ => none)
      (clockLocations (List.replicate p.degree 0)) (some 0) ready.work := by
    change PolynomialClockMemory M p _ _ _ _ atOrigin.work
    rw [originMemory]; exact memory
  have table : C.transition ready.state w[ready.inputHead]? none none (ready.work ready.workHead) =
      .step (sequenceControl L routine (.inr (2 : Fin 3))) none .stay .stay .stay .stay none := by
    simp [C, L, clockPreparedLoader, sequenceMachine, ready, sequenceRightConfiguration, routine, machineRoutine,
      clockInputReset, originState, originHead, originMemory, memory 0, polynomialClockCell, sequenceRightInstruction]
  refine ⟨ready, originHead, originInput, originAux.trans auxiliary, originIndex.trans index,
    originRandom.trans random, originOutput.trans output, prepared, table, ?_⟩
  have simulation := sequence_right_runFrom L routine data bits entered (2 * (w.length + 1) + 1)
  change C.runFrom data bits (sequenceRightConfiguration L routine entered) _ =
    sequenceRightResult L routine (R.runFrom data bits entered _) at simulation
  rw [resetRun] at simulation
  have total : 6 * w.length + 13 = (4 * w.length + 10) + (2 * (w.length + 1) + 1) := by omega
  change C.run data bits _ = _
  rw [total, ← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ (4 * w.length + 10)
    (by simpa using loaded)]
  exact simulation

theorem polynomialClockMachine_loaded (w : List I) (bits : BitString) :
    ∃ ready : Configuration (polynomialClockCore M p),
      ClockReady M p (w.length + 1) (List.replicate p.degree 0) ⟨p.coefficient, by omega⟩
        M.initialConfiguration false ready ∧
      (polynomialClockMachine M p).run (decisionData w) bits (6 * w.length + 15) =
        (polynomialClockMachine M p).observe (decisionData w) bits
          (sequenceRightConfiguration (clockPreparedLoader M p) (polynomialClockRoutine M p) ready) := by
  let L := clockPreparedLoader M p
  let routine := polynomialClockRoutine M p
  let C := polynomialClockMachine M p
  let data := decisionData w
  obtain ⟨prepared, head, input, auxiliary, index, random, output, memory, table, loaded⟩ :=
    clock_prepared_loader M p w bits
  let finalState := sequenceControl (clockLoader M p) (machineRoutine (clockInputReset M p)) (.inr (2 : Fin 3))
  let done := L.stepConfiguration data prepared finalState none .stay .stay .stay .stay none
  have sourceTable : L.transition prepared.state data.input[prepared.inputHead]? data.auxiliary[prepared.auxiliaryHead]?
      (if prepared.indexHead < data.index then some () else none) (prepared.work prepared.workHead) =
      .step finalState none .stay .stay .stay .stay none := by
    simpa [data, decisionData] using table
  have sourceLive := L.observe_step data bits prepared _ _ _ _ _ _ _ sourceTable
  have sourceNext := L.next_step data bits prepared _ _ _ _ _ _ _ sourceTable
  have accepts : L.transition done.state data.input[done.inputHead]? data.auxiliary[done.auxiliaryHead]?
      (if done.indexHead < data.index then some () else none) (done.work done.workHead) = .accept := by
    simp [L, clockPreparedLoader, done, Machine.stepConfiguration, finalState,
      sequenceMachine, machineRoutine, clockInputReset, sequenceRightInstruction]
  let ready := handoffConfiguration L routine data done []
  have related : ClockReady M p (w.length + 1) (List.replicate p.degree 0) ⟨p.coefficient, by omega⟩
      M.initialConfiguration false ready := by
    refine ⟨⟨memory, random, rfl, ?_, ?_, ?_⟩, rfl, ?_, by simp [Machine.initialConfiguration]⟩
    · simp [ready, handoffConfiguration, done, Machine.stepConfiguration, input, Move.onInput, Machine.initialConfiguration]
    · simp [ready, handoffConfiguration, done, Machine.stepConfiguration, auxiliary, Move.onInput, Machine.initialConfiguration]
    · simp [ready, handoffConfiguration, done, Machine.stepConfiguration, index, Move.onInput, Machine.initialConfiguration]
    · simpa [ready, handoffConfiguration, done, Machine.stepConfiguration, Move.onInt, Machine.initialConfiguration] using head
  have live := sequence_left_observe L routine data bits prepared [] sourceLive
  have next := sequence_left_next L routine data bits prepared done [] sourceNext
  have doneRun : C.runFrom data bits (sequenceLeftConfiguration L routine prepared []) 1 =
      C.observe data bits (sequenceLeftConfiguration L routine done []) :=
    C.runFrom_shift data bits _ _ live next 0
  have handoffRun := sequence_accept_handoff L routine data bits done [] accepts
  have loadedPrefix := sequence_left_running L routine data bits L.initialConfiguration prepared [] (6 * w.length + 13)
    (by simpa using loaded)
  have initial : sequenceLeftConfiguration L routine L.initialConfiguration [] = C.initialConfiguration := rfl
  rw [initial] at loadedPrefix
  have prefixRun : C.runFrom data bits C.initialConfiguration (6 * w.length + 13) =
      C.observe data bits (sequenceLeftConfiguration L routine prepared []) := loadedPrefix.trans live.symm
  refine ⟨ready, related, ?_⟩
  have total : 6 * w.length + 15 = (6 * w.length + 13) + (1 + 1) := by omega
  change C.run data bits _ = _
  rw [total, ← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ _ prefixRun,
    C.runFrom_add data bits _ _ 1 doneRun]
  exact handoffRun

end

end ComplexityOfGenerators.Simulation
