import ComplexityOfGenerators.Simulation.GeneratorRecognizer

/-! Connecting the verified block loader and input-reset scans to the actual
blank-tape initial configuration of the generator recognizer. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

theorem wordIndex_reset_entry (w : List α) (bits : BitString) :
    ∃ ready : Configuration (indexInputReset M),
      ready.state = (0 : Fin 4) ∧ ready.workHead = 0 ∧ ready.inputHead ≤ w.length ∧
      ready.auxiliaryHead = 0 ∧ ready.indexHead = 0 ∧ ready.randomHead = 0 ∧ ready.output = [] ∧
      VirtualIndexMemory M (w.length + 1) (fun _ => none)
        (some 0) (some 0) ready.work ∧
      (wordIndexPreparedLoader M).run (decisionData w) bits (4 * w.length + 8) =
        (wordIndexPreparedLoader M).observe (decisionData w) bits
          (sequenceRightConfiguration (wordIndexLoader M) (machineRoutine (indexInputReset M)) ready) := by
  let L := wordIndexLoader M
  let routine := machineRoutine (indexInputReset M)
  let C := wordIndexPreparedLoader M
  let data := decisionData w
  obtain ⟨marker, markerState, markerHead, markerMemory, _, markerRun⟩ :=
    block_at_marker (indexLoaderProgram M) (Fintype.equivFin Unit) (indexAlphabet M) (wordIndexBlocks M) w bits
  change Configuration L at marker
  have time : 2 * ((wordIndexBlocks M).word w).length + 2 * w.length + 4 = 4 * w.length + 6 := by simp; omega
  rw [time] at markerRun
  have atMarker : L.run data bits (4 * w.length + 6) = .running marker := markerRun
  have markerRandom := L.deterministic_running_randomHead
    (blockMachine_deterministic (indexLoaderProgram M) (Fintype.equivFin Unit) (indexAlphabet M) (wordIndexBlocks M))
    data bits _ marker atMarker
  have markerRead : marker.work marker.workHead = some (Fin.last (Fintype.card (IndexCell M.symbols))) := by
    rw [markerHead, markerMemory]
    simp [bootMemory]
  let done := L.stepConfiguration data marker
    (blockControl (wordIndexBlocks M) (.run ((Fintype.equivFin Unit) ()))) none .right .stay .stay .stay none
  have table : L.transition marker.state data.input[marker.inputHead]? data.auxiliary[marker.auxiliaryHead]?
      (if marker.indexHead < data.index then some true else none) (marker.work marker.workHead) =
      .step (blockControl (wordIndexBlocks M) (.run ((Fintype.equivFin Unit) ()))) none .right .stay .stay .stay none := by
    simp [L, wordIndexLoader, blockMachine, blockTransition, markerState, markerRead]
  have markerLive := L.observe_step data bits marker _ _ _ _ _ _ _ table
  have markerNext := L.next_step data bits marker _ _ _ _ _ _ _ table
  have accepts : L.transition done.state data.input[done.inputHead]? data.auxiliary[done.auxiliaryHead]?
      (if done.indexHead < data.index then some true else none) (done.work done.workHead) = .accept := by
    simp [L, wordIndexLoader, done, Machine.stepConfiguration, blockMachine, blockTransition, indexLoaderProgram, postInstruction]
  let ready : Configuration (indexInputReset M) := handoffConfiguration L routine data done []
  have head : ready.workHead = 0 := by
    simp [ready, handoffConfiguration, done, Machine.stepConfiguration, Move.onInt, markerHead]
  have prepared : VirtualIndexMemory M (w.length + 1) (fun _ => none)
      (some 0) (some 0) ready.work := by
    change VirtualIndexMemory M _ _ _ _ marker.work
    rw [markerMemory, wordIndexBlocks_word]
    simpa only [List.length_cons, List.length_append, List.length_replicate, List.length_singleton,
      List.length_nil, Nat.zero_add, Nat.add_assoc] using initial_index_memory M w.length
  have live := sequence_left_observe L routine data bits marker [] markerLive
  have next := sequence_left_next L routine data bits marker done [] markerNext
  have enterRun : C.runFrom data bits (sequenceLeftConfiguration L routine marker []) 1 =
      C.observe data bits (sequenceLeftConfiguration L routine done []) :=
    C.runFrom_shift data bits _ _ live next 0
  have handoffRun := sequence_accept_handoff L routine data bits done [] accepts
  have loadedPrefix := sequence_left_running L routine data bits L.initialConfiguration marker [] (4 * w.length + 6)
    (by simpa using atMarker)
  have initial : sequenceLeftConfiguration L routine L.initialConfiguration [] = C.initialConfiguration := rfl
  rw [initial] at loadedPrefix
  have prefixRun : C.runFrom data bits C.initialConfiguration (4 * w.length + 6) =
      C.observe data bits (sequenceLeftConfiguration L routine marker []) := loadedPrefix.trans live.symm
  refine ⟨ready, rfl, head, ?_, ?_, ?_, markerRandom, rfl, prepared, ?_⟩
  · exact Nat.min_le_right _ _
  · simp [ready, handoffConfiguration, data, decisionData, Move.onInput]
  · simp [ready, handoffConfiguration, data, decisionData, Move.onInput]
  · have total : 4 * w.length + 8 = (4 * w.length + 6) + (1 + 1) := by omega
    change C.run data bits _ = _
    rw [total, ← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ _ prefixRun,
      C.runFrom_add data bits _ _ 1 enterRun]
    exact handoffRun

theorem wordIndex_prepared_loader (w : List α) (bits : BitString) :
    ∃ ready : Configuration (wordIndexPreparedLoader M),
      ready.workHead = 0 ∧ ready.inputHead = 0 ∧ ready.auxiliaryHead = 0 ∧ ready.indexHead = 0 ∧
      ready.randomHead = 0 ∧ ready.output = [] ∧
      VirtualIndexMemory M w.length (fun _ => none)
        (some 0) (some 0) ready.work ∧
      (wordIndexPreparedLoader M).transition ready.state w[ready.inputHead]? none none (ready.work ready.workHead) =
        .step (sequenceControl (wordIndexLoader M) (machineRoutine (indexInputReset M)) (.inr (3 : Fin 4)))
          none .stay .stay .stay .stay none ∧
      (wordIndexPreparedLoader M).run (decisionData w) bits (6 * w.length + 11) = .running ready := by
  let L := wordIndexLoader M
  let routine := machineRoutine (indexInputReset M)
  let R := indexInputReset M
  let C := wordIndexPreparedLoader M
  let data := decisionData w
  obtain ⟨entered, state, head, input, auxiliary, index, random, output, memory, loaded⟩ := wordIndex_reset_entry M w bits
  have bounds : ReadHeadBounds R data entered := ⟨input, by simp [auxiliary, data, decisionData], by simp [index, data, decisionData]⟩
  obtain ⟨atOrigin, originState, originHead, originInput, originMemory, originRandom, originOutput,
      originAux, originIndex, resetRun⟩ := index_input_reset M data bits w.length (fun _ => none) (some 0) (some 0) entered bounds input state head memory
  let ready := sequenceRightConfiguration L routine atOrigin
  have prepared : VirtualIndexMemory M w.length (fun _ => none)
      (some 0) (some 0) ready.work := by
    change VirtualIndexMemory M _ _ _ _ atOrigin.work
    exact originMemory
  have table : C.transition ready.state w[ready.inputHead]? none none (ready.work ready.workHead) =
      .step (sequenceControl L routine (.inr (3 : Fin 4))) none .stay .stay .stay .stay none := by
    simp [C, L, wordIndexPreparedLoader, sequenceMachine, ready, sequenceRightConfiguration, routine, machineRoutine,
      indexInputReset, originState, originHead, originMemory 0, virtualIndexCell, sequenceRightInstruction]
  refine ⟨ready, originHead, originInput, originAux.trans auxiliary, originIndex.trans index,
    originRandom.trans random, originOutput.trans output, prepared, table, ?_⟩
  have simulation := sequence_right_runFrom L routine data bits entered (2 * w.length + 3)
  change C.runFrom data bits (sequenceRightConfiguration L routine entered) _ =
    sequenceRightResult L routine (R.runFrom data bits entered _) at simulation
  rw [resetRun] at simulation
  have total : 6 * w.length + 11 = (4 * w.length + 8) + (2 * w.length + 3) := by omega
  change C.run data bits _ = _
  rw [total, ← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ (4 * w.length + 8)
    (by simpa using loaded)]
  exact simulation

theorem generatorRecognizer_loaded (w : List α) (bits : BitString) :
    ∃ coreReady : Configuration (virtualIndexCore M),
      IndexReady M w.length M.initialConfiguration false coreReady ∧
      (generatorRecognizer M).run (decisionData w) bits (6 * w.length + 13) =
        (generatorRecognizer M).observe (decisionData w) bits
          (sequenceRightConfiguration (wordIndexPreparedLoader M) (generatorMatcherRoutine M)
            (matcherConfiguration (virtualIndexCore M) w coreReady)) := by
  classical
  let L := wordIndexPreparedLoader M
  let routine := generatorMatcherRoutine M
  let C := generatorRecognizer M
  let data := decisionData w
  obtain ⟨prepared, head, input, auxiliary, index, random, output, memory, table, loaded⟩ :=
    wordIndex_prepared_loader M w bits
  let finalState := sequenceControl (wordIndexLoader M) (machineRoutine (indexInputReset M)) (.inr (3 : Fin 4))
  let done := L.stepConfiguration data prepared finalState none .stay .stay .stay .stay none
  have sourceTable : L.transition prepared.state data.input[prepared.inputHead]? data.auxiliary[prepared.auxiliaryHead]?
      (if prepared.indexHead < data.index then some true else none) (prepared.work prepared.workHead) =
      .step finalState none .stay .stay .stay .stay none := by simpa [data, decisionData] using table
  have sourceLive := L.observe_step data bits prepared _ _ _ _ _ _ _ sourceTable
  have sourceNext := L.next_step data bits prepared _ _ _ _ _ _ _ sourceTable
  have accepts : L.transition done.state data.input[done.inputHead]? data.auxiliary[done.auxiliaryHead]?
      (if done.indexHead < data.index then some true else none) (done.work done.workHead) = .accept := by
    simp [L, wordIndexPreparedLoader, done, Machine.stepConfiguration, finalState,
      sequenceMachine, machineRoutine, indexInputReset, sequenceRightInstruction]
  let targetReady := handoffConfiguration L routine data done []
  let coreReady : Configuration (virtualIndexCore M) := {
    state := (virtualIndexCore M).initial
    inputHead := 0
    auxiliaryHead := 0
    indexHead := 0
    randomHead := 0
    workHead := 0
    work := prepared.work
    visited := targetReady.visited
    output := [] }
  have related : IndexReady M w.length M.initialConfiguration false coreReady :=
    ⟨⟨memory, rfl, rfl⟩, rfl, rfl, by simp [Machine.initialConfiguration]⟩
  have targetEq : targetReady = matcherConfiguration (virtualIndexCore M) w coreReady := by
    simp [targetReady, handoffConfiguration, done, Machine.stepConfiguration, head, input, auxiliary, index, random,
      Move.onInput, Move.onInt, coreReady, matcherConfiguration, routine, generatorMatcherRoutine, machineRoutine, outputMatcher]
  have live := sequence_left_observe L routine data bits prepared [] sourceLive
  have next := sequence_left_next L routine data bits prepared done [] sourceNext
  have doneRun : C.runFrom data bits (sequenceLeftConfiguration L routine prepared []) 1 =
      C.observe data bits (sequenceLeftConfiguration L routine done []) :=
    C.runFrom_shift data bits _ _ live next 0
  have handoffRun := sequence_accept_handoff L routine data bits done [] accepts
  have loadedPrefix := sequence_left_running L routine data bits L.initialConfiguration prepared [] (6 * w.length + 11)
    (by simpa using loaded)
  have initial : sequenceLeftConfiguration L routine L.initialConfiguration [] = C.initialConfiguration := rfl
  rw [initial] at loadedPrefix
  have prefixRun : C.runFrom data bits C.initialConfiguration (6 * w.length + 11) =
      C.observe data bits (sequenceLeftConfiguration L routine prepared []) := loadedPrefix.trans live.symm
  refine ⟨coreReady, related, ?_⟩
  have total : 6 * w.length + 13 = (6 * w.length + 11) + (1 + 1) := by omega
  change C.run data bits _ = _
  rw [total, ← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ _ prefixRun,
    C.runFrom_add data bits _ _ 1 doneRun]
  exact handoffRun.trans (congrArg (fun c => C.observe data bits (sequenceRightConfiguration L routine c)) targetEq)

end

end ComplexityOfGenerators.Simulation
