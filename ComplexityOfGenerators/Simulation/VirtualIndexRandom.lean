import ComplexityOfGenerators.Simulation.VirtualIndexStep

/-! Random transitions of the concrete virtual-index routine consume exactly
one source random bit. All scans and phase changes preserve the random position. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

theorem index_fetched_random (data : InputData Unit Bool) (bits : BitString) (length : ℕ)
    (source : Configuration M) (negative : Bool) (distance : ℕ)
    (position : source.workHead = signedPosition negative distance)
    (target : Configuration (virtualIndexCore M)) (related : IndexFetched M length source negative target)
    (no yes : Fin M.states) (bit : Bool)
    (instruction : M.transition source.state none none
      (if source.indexHead < length then some true else none) (source.work source.workHead) = .readRandom no yes)
    (read : bits[source.randomHead]? = some bit) :
    ∃ ready newNegative,
      IndexReady M length {source with state := if bit then yes else no, randomHead := source.randomHead + 1}
        newNegative ready ∧
      (virtualIndexCore M).runFrom data bits target (source.indexHead + distance + 5) =
        (virtualIndexCore M).observe data bits ready := by
  let N := virtualIndexCore M
  let nextState := if bit then yes else no
  let action := indexResume M nextState
  let consumed : Configuration N := {target with
    state := indexControl M (.returnOrigin action negative)
    randomHead := target.randomHead + 1}
  have readTable : N.transition target.state data.input[target.inputHead]?
      data.auxiliary[target.auxiliaryHead]?
      (if target.indexHead < data.index then some true else none) (target.work target.workHead) =
      .readRandom (indexControl M (.returnOrigin (indexResume M no) negative))
        (indexControl M (.returnOrigin (indexResume M yes) negative)) := by
    have readCell := related.memory (source.indexHead : ℤ)
    simp [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
      related.state, related.head, readCell, virtualIndexCell, instruction]
  have available : source.randomHead < bits.length := by
    by_contra unavailable
    have missing : bits[source.randomHead]? = none := List.getElem?_eq_none_iff.mpr (by omega)
    rw [missing] at read
    cases read
  have readLive : N.observe data bits target = .running target := by
    simp [Machine.observe, readTable, related.random, available]
  have readNext : N.next data bits target = .running consumed := by
    simp only [Machine.next, readTable, related.random, read]
    cases bit <;> simp [consumed, action, nextState, related.random]
  have readRun : N.runFrom data bits target 1 = N.observe data bits consumed :=
    N.runFrom_shift data bits target consumed readLive readNext 0
  obtain ⟨ready, readyState, readyHead, readyMemory, readyRandom, readyOutput, returnRun⟩ :=
    index_return M data bits length source.work source.indexHead source.workHead action negative distance position
      consumed related.memory rfl related.head
  let newNegative := workSideAfter M
    (virtualIndexCell M length source.work (some source.indexHead) (some source.workHead) source.workHead)
    negative .stay
  refine ⟨ready, newNegative, ⟨⟨?_, ?_, ?_⟩, readyState, readyHead, ?_⟩, ?_⟩
  · simpa [indexActionValue, action, indexResume, Move.onInt] using readyMemory
  · exact readyRandom.trans (congrArg (fun n => n + 1) related.random)
  · exact readyOutput.trans related.output
  · exact workSideAfter_correct M length source.work _ _ source.workHead negative .stay related.side
  · have clock : source.indexHead + distance + 5 = 1 + (source.indexHead + distance + 4) := by omega
    rw [clock, N.runFrom_add data bits target consumed 1 readRun]
    exact returnRun

end

end ComplexityOfGenerators.Simulation
