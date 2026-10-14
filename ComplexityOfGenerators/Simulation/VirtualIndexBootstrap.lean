import ComplexityOfGenerators.Simulation.VirtualIndexLoader

/-! The complete affine-index adapter enters its simulation routine after a
linear-time bootstrap from the actual blank initial work tape. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

theorem collisionIndex_loaded (n : ℕ) (bits : BitString) :
    ∃ ready : Configuration (virtualIndexCore M),
      IndexReady M (4 * (n + 1) + 2) M.initialConfiguration false ready ∧
      (sequenceMachine (indexLoader M) (virtualIndexRoutine M)).run (decisionData (List.replicate n ())) bits
        (10 * n + 18) =
      (sequenceMachine (indexLoader M) (virtualIndexRoutine M)).observe (decisionData (List.replicate n ())) bits
        (sequenceRightConfiguration (indexLoader M) (virtualIndexRoutine M) ready) := by
  let L := indexLoader M
  let routine := virtualIndexRoutine M
  let C := sequenceMachine L routine
  let data := decisionData (List.replicate n ())
  obtain ⟨marker, markerState, markerHead, markerMemory, _, markerRun⟩ :=
    block_at_marker (indexLoaderProgram M) (Fintype.equivFin Unit) (indexAlphabet M)
      (collisionIndexBlocks M) (List.replicate n ()) bits
  change Configuration L at marker
  have clock : 2 * ((collisionIndexBlocks M).word (List.replicate n ())).length +
      2 * (List.replicate n ()).length + 4 = 10 * n + 16 := by
    simp only [collisionIndexBlocks_word, List.length_cons, List.length_replicate]
    omega
  rw [clock] at markerRun
  have atMarker : L.run data bits (10 * n + 16) = .running marker := markerRun
  have deterministic : L.Deterministic :=
    blockMachine_deterministic (indexLoaderProgram M) (Fintype.equivFin Unit)
      (indexAlphabet M) (collisionIndexBlocks M)
  have markerRandom := L.deterministic_running_randomHead deterministic data bits _ marker atMarker
  have markerRead : marker.work marker.workHead = some (Fin.last (Fintype.card (IndexCell M.symbols))) := by
    rw [markerHead, markerMemory]
    simp [bootMemory]
  let sourceReady := L.stepConfiguration data marker
    (blockControl (collisionIndexBlocks M) (.run ((Fintype.equivFin Unit) ())))
    none .right .stay .stay .stay none
  have markerTable : L.transition marker.state data.input[marker.inputHead]?
      data.auxiliary[marker.auxiliaryHead]?
      (if marker.indexHead < data.index then some () else none) (marker.work marker.workHead) =
      .step (blockControl (collisionIndexBlocks M) (.run ((Fintype.equivFin Unit) ())))
        none .right .stay .stay .stay none := by
    simp [L, indexLoader, blockMachine, blockTransition, markerState, markerRead]
  have markerLive := L.observe_step data bits marker _ _ _ _ _ _ _ markerTable
  have markerNext := L.next_step data bits marker _ _ _ _ _ _ _ markerTable
  have acceptTable : L.transition sourceReady.state data.input[sourceReady.inputHead]?
      data.auxiliary[sourceReady.auxiliaryHead]?
      (if sourceReady.indexHead < data.index then some () else none) (sourceReady.work sourceReady.workHead) =
      .accept := by
    simp [L, indexLoader, sourceReady, Machine.stepConfiguration, blockMachine, blockTransition,
      indexLoaderProgram, postInstruction]
  let ready := handoffConfiguration L routine data sourceReady []
  have prepared : IndexReady M (4 * (n + 1) + 2) M.initialConfiguration false ready := by
    refine ⟨⟨?_, markerRandom, rfl⟩, rfl, ?_, by simp [Machine.initialConfiguration]⟩
    · change VirtualIndexMemory M (4 * (n + 1) + 2) (fun _ => none) (some 0) (some 0) marker.work
      rw [markerMemory, collisionIndexBlocks_word]
      have size : 4 * (n + 1) + 2 = (5 + 4 * n) + 1 := by omega
      rw [size]
      simpa only [List.length_cons, List.length_replicate] using initial_index_memory M (5 + 4 * n)
    · simp [ready, handoffConfiguration, sourceReady, Machine.stepConfiguration, Move.onInt, markerHead,
        Machine.initialConfiguration]
  have combinedLive := sequence_left_observe L routine data bits marker [] markerLive
  have combinedNext := sequence_left_next L routine data bits marker sourceReady [] markerNext
  have enterRun : C.runFrom data bits (sequenceLeftConfiguration L routine marker []) 1 =
      C.observe data bits (sequenceLeftConfiguration L routine sourceReady []) :=
    C.runFrom_shift data bits _ _ combinedLive combinedNext 0
  have handoffRun := sequence_accept_handoff L routine data bits sourceReady [] acceptTable
  have prefixRun := sequence_left_running L routine data bits L.initialConfiguration marker [] (10 * n + 16)
    (by simpa using atMarker)
  have initial : sequenceLeftConfiguration L routine L.initialConfiguration [] = C.initialConfiguration := rfl
  rw [initial] at prefixRun
  have prefixObservation : C.runFrom data bits C.initialConfiguration (10 * n + 16) =
      C.observe data bits (sequenceLeftConfiguration L routine marker []) := prefixRun.trans combinedLive.symm
  refine ⟨ready, prepared, ?_⟩
  change C.run data bits (10 * n + 18) = _
  have total : 10 * n + 18 = (10 * n + 16) + (1 + 1) := by omega
  rw [total, ← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ _ prefixObservation,
    C.runFrom_add data bits _ _ 1 enterRun]
  exact handoffRun

/-- End-to-end simulation, including input expansion, work-tape initialisation,
both virtual heads, all output, and the original finite random tape. -/
theorem collisionIndexMachine_run (n t : ℕ) (bits : BitString) (result : Outcome O)
    (execution : M.run (generatorData (4 * (n + 1) + 2)) bits t = .halted result) :
    (collisionIndexMachine M).run (generatorData n) bits
      (10 * n + 18 + (t + 1) * (2 * t + 2 * (4 * (n + 1) + 2) + 8)) = .halted result := by
  let C := sequenceMachine (indexLoader M) (virtualIndexRoutine M)
  let data := decisionData (List.replicate n ())
  obtain ⟨ready, related, loaded⟩ := collisionIndex_loaded M n bits
  have simulated := index_simulates_run M data bits (4 * (n + 1) + 2) t ready related result execution
  have lifted := sequence_right_runFrom (indexLoader M) (virtualIndexRoutine M) data bits ready
    ((t + 1) * (2 * t + 2 * (4 * (n + 1) + 2) + 8))
  rw [simulated] at lifted
  have combined := C.runFrom_add data bits C.initialConfiguration
    (sequenceRightConfiguration (indexLoader M) (virtualIndexRoutine M) ready) (10 * n + 18)
    (by simpa using loaded) ((t + 1) * (2 * t + 2 * (4 * (n + 1) + 2) + 8))
  rw [Machine.runFrom_initial, lifted] at combined
  change (unarySwapMachine C).run (generatorData n) bits _ = _
  rw [← unarySwap_decisionData n, unarySwap_run]
  change unarySwapResult C (C.run data bits _) = _
  rw [combined]
  rfl

end

end ComplexityOfGenerators.Simulation
