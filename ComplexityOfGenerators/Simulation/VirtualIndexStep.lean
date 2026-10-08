import ComplexityOfGenerators.Simulation.VirtualIndexReturn

/-! Simulation of a source work/output transition, including the independently
moving and clamped virtual index head. All administrative steps are counted. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

theorem index_fetched_step (data : InputData Unit Bool) (bits : BitString) (length : ℕ)
    (source : Configuration M) (negative : Bool) (distance : ℕ)
    (position : source.workHead = signedPosition negative distance)
    (bounded : source.indexHead ≤ length)
    (target : Configuration (virtualIndexCore M)) (related : IndexFetched M length source negative target)
    (next : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (instruction : M.transition source.state none none
      (if source.indexHead < length then some true else none) (source.work source.workHead) =
      .step next write work input auxiliary index emit) :
    ∃ ready newNegative,
      IndexReady M length (M.stepConfiguration (generatorData length) source next write work input auxiliary index emit)
        newNegative ready ∧
      (virtualIndexCore M).runFrom data bits target (index.onInput length source.indexHead + distance + 6) =
        (virtualIndexCore M).observe data bits ready := by
  let N := virtualIndexCore M
  let action : IndexAction O M.states M.symbols := ⟨next, write, work, emit⟩
  let cell := virtualIndexCell M length source.work (some source.indexHead) (some source.workHead) source.indexHead
  let newIndex := index.onInput length source.indexHead
  let cleared := N.stepConfiguration data target (indexControl M (.placeIndex action negative))
    (some (indexWrite M {cell with indexHead := false})) (virtualIndexMove M cell index)
    .stay .stay .stay none
  have clearTable : N.transition target.state data.input[target.inputHead]?
      data.auxiliary[target.auxiliaryHead]?
      (if target.indexHead < data.index then some true else none) (target.work target.workHead) =
      .step (indexControl M (.placeIndex action negative))
        (some (indexWrite M {cell with indexHead := false})) (virtualIndexMove M cell index)
        .stay .stay .stay none := by
    have readCell := related.memory (source.indexHead : ℤ)
    simp [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
      related.state, related.head, readCell, virtualIndexCell, instruction, action, cell]
  have clearLive := N.observe_step data bits target _ _ _ _ _ _ _ clearTable
  have clearNext := N.next_step data bits target _ _ _ _ _ _ _ clearTable
  have clearRun : N.runFrom data bits target 1 = N.observe data bits cleared :=
    N.runFrom_shift data bits target cleared clearLive clearNext 0
  have clearedHead : cleared.workHead = (newIndex : ℤ) := by
    change (virtualIndexMove M cell index).onInt target.workHead = _
    rw [related.head]
    exact virtualIndexMove_correct M length source.indexHead bounded source.work _ _ index
  have clearedMemory : VirtualIndexMemory M length source.work none (some source.workHead) cleared.work := by
    have erased := related.memory.clear_index M (source.indexHead : ℤ)
    simpa only [cleared, Machine.stepConfiguration, related.head, related.memory (source.indexHead : ℤ)] using erased
  let placed := N.stepConfiguration data cleared (indexControl M (.returnOrigin action negative))
    (some (indexWrite M {indexRead M (cleared.work cleared.workHead) with indexHead := true}))
    .stay .stay .stay .stay none
  have placeTable : N.transition cleared.state data.input[cleared.inputHead]?
      data.auxiliary[cleared.auxiliaryHead]?
      (if cleared.indexHead < data.index then some true else none) (cleared.work cleared.workHead) =
      .step (indexControl M (.returnOrigin action negative))
        (some (indexWrite M {indexRead M (cleared.work cleared.workHead) with indexHead := true}))
        .stay .stay .stay .stay none := by
    simp only [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, cleared, Machine.stepConfiguration,
      Equiv.symm_apply_apply, virtualIndexTransition]
  have placeLive := N.observe_step data bits cleared _ _ _ _ _ _ _ placeTable
  have placeNext := N.next_step data bits cleared _ _ _ _ _ _ _ placeTable
  have placeRun : N.runFrom data bits cleared 1 = N.observe data bits placed :=
    N.runFrom_shift data bits cleared placed placeLive placeNext 0
  have placedMemory : VirtualIndexMemory M length source.work (some newIndex) (some source.workHead) placed.work := by
    have installed := clearedMemory.place_index M (newIndex : ℤ)
    simpa only [placed, Machine.stepConfiguration, clearedHead] using installed
  obtain ⟨ready, readyState, readyHead, readyMemory, readyRandom, readyOutput, returnRun⟩ :=
    index_return M data bits length source.work newIndex source.workHead action negative distance position placed
      placedMemory rfl clearedHead
  let newNegative := workSideAfter M
    (virtualIndexCell M length source.work (some newIndex) (some source.workHead) source.workHead) negative work
  refine ⟨ready, newNegative, ⟨⟨?_, readyRandom.trans related.random, ?_⟩, readyState, readyHead, ?_⟩, ?_⟩
  · cases write <;>
      simpa [Machine.stepConfiguration, generatorData, indexActionValue, action, newIndex] using readyMemory
  · cases emit <;>
      simpa only [indexActionOutput, action, placed, cleared, Machine.stepConfiguration, related.output] using readyOutput
  · exact workSideAfter_correct M length source.work _ _ source.workHead negative work related.side
  · have clock : index.onInput length source.indexHead + distance + 6 = 1 + (1 + (newIndex + distance + 4)) := by
      dsimp [newIndex]
      omega
    rw [clock, N.runFrom_add data bits target cleared 1 clearRun,
      N.runFrom_add data bits cleared placed 1 placeRun]
    exact returnRun

end

end ComplexityOfGenerators.Simulation
