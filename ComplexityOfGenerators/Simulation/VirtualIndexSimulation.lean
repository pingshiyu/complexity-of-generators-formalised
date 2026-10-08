import ComplexityOfGenerators.Simulation.VirtualIndexRandom
import ComplexityOfGenerators.Foundations.ExecutionBounds

/-! Complete source-transition simulation by the concrete virtual-index core.
The overhead is bounded in terms of the source work-head distance and the unary
index length, not by an uncharged operation on a configuration. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

theorem signedPosition_natAbs (head : ℤ) (negative : Bool)
    (side : if negative then head ≤ 0 else 0 ≤ head) :
    head = signedPosition negative head.natAbs := by
  cases negative <;> cases head <;> simp_all [signedPosition]
  all_goals omega

/-- One source transition has a concrete native simulation using at most
`2 * |workHead| + 2 * indexLength + 8` primitive transitions. -/
theorem index_simulates_next (data : InputData Unit Bool) (bits : BitString) (length : ℕ)
    (source nextSource : Configuration M) (negative : Bool)
    (target : Configuration (virtualIndexCore M)) (related : IndexReady M length source negative target)
    (bounded : source.indexHead ≤ length)
    (step : M.next (generatorData length) bits source = .running nextSource) :
    ∃ t ready newNegative,
      t ≤ 2 * source.workHead.natAbs + 2 * length + 8 ∧
      IndexReady M length nextSource newNegative ready ∧
      (virtualIndexCore M).runFrom data bits target t = (virtualIndexCore M).observe data bits ready := by
  let distance := source.workHead.natAbs
  have position : source.workHead = signedPosition negative distance := signedPosition_natAbs _ _ related.side
  obtain ⟨fetched, fetchedRelated, fetchRun⟩ := index_fetch M data bits length source negative distance position target related
  cases instruction : M.transition source.state none none
      (if source.indexHead < length then some true else none) (source.work source.workHead) with
  | accept => simp [Machine.next, generatorData, instruction] at step
  | reject => simp [Machine.next, generatorData, instruction] at step
  | step next write work input auxiliary index emit =>
      have native := M.next_step (generatorData length) bits source next write work input auxiliary index emit
        (by simpa [generatorData] using instruction)
      have same := RunState.running.inj (step.symm.trans native)
      subst nextSource
      obtain ⟨ready, newNegative, readyRelated, returnRun⟩ := index_fetched_step M data bits length source negative
        distance position bounded fetched fetchedRelated next write work input auxiliary index emit instruction
      refine ⟨(distance + source.indexHead + 2) + (index.onInput length source.indexHead + distance + 6),
        ready, newNegative, ?_, readyRelated, ?_⟩
      · have bound := index.onInput_le length source.indexHead bounded
        dsimp [distance]
        omega
      · rw [(virtualIndexCore M).runFrom_add data bits target fetched _ fetchRun]
        exact returnRun
  | readRandom no yes =>
      cases read : bits[source.randomHead]? with
      | none => simp [Machine.next, generatorData, instruction, read] at step
      | some bit =>
          have same : {source with state := if bit then yes else no, randomHead := source.randomHead + 1} = nextSource := by
            simpa [Machine.next, generatorData, instruction, read] using step
          subst nextSource
          obtain ⟨ready, newNegative, readyRelated, returnRun⟩ := index_fetched_random M data bits length source negative
            distance position fetched fetchedRelated no yes bit instruction read
          refine ⟨(distance + source.indexHead + 2) + (source.indexHead + distance + 5),
            ready, newNegative, ?_, readyRelated, ?_⟩
          · dsimp [distance]
            omega
          · rw [(virtualIndexCore M).runFrom_add data bits target fetched _ fetchRun]
            exact returnRun

/-- A terminal source observation is reproduced after the bounded fetch trip. -/
theorem index_simulates_observe_halted (data : InputData Unit Bool) (bits : BitString) (length : ℕ)
    (source : Configuration M) (negative : Bool) (target : Configuration (virtualIndexCore M))
    (related : IndexReady M length source negative target) (result : Outcome O)
    (halted : M.observe (generatorData length) bits source = .halted result) :
    (virtualIndexCore M).runFrom data bits target (source.workHead.natAbs + source.indexHead + 2) = .halted result := by
  have position := signedPosition_natAbs source.workHead negative related.side
  obtain ⟨fetched, fetchedRelated, execution⟩ := index_fetch M data bits length source negative
    source.workHead.natAbs position target related
  rw [execution, index_fetched_observe M data bits length source negative fetched fetchedRelated, halted]
  rfl

end

end ComplexityOfGenerators.Simulation
