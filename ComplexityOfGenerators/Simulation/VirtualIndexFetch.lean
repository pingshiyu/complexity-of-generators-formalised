import ComplexityOfGenerators.Simulation.VirtualIndexScan

/-!
# Fetching a source instruction through the virtual index

The source work symbol is cached in finite control while the routine visits the
virtual index head. This module proves the complete trip, its exact cost, and
correspondence of terminal observations, including random-tape exhaustion.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

structure IndexSnapshot (length : ℕ) (source : Configuration M)
    (target : Configuration (virtualIndexCore M)) : Prop where
  memory : VirtualIndexMemory M length source.work (some source.indexHead) (some source.workHead) target.work
  random : target.randomHead = source.randomHead
  output : target.output = source.output

structure IndexReady (length : ℕ) (source : Configuration M) (negative : Bool)
    (target : Configuration (virtualIndexCore M)) : Prop extends IndexSnapshot M length source target where
  state : target.state = indexControl M (.source source.state negative)
  head : target.workHead = source.workHead
  side : if negative then source.workHead ≤ 0 else 0 ≤ source.workHead

structure IndexFetched (length : ℕ) (source : Configuration M) (negative : Bool)
    (target : Configuration (virtualIndexCore M)) : Prop extends IndexSnapshot M length source target where
  state : target.state = indexControl M (.toIndex source.state negative (source.work source.workHead))
  head : target.workHead = (source.indexHead : ℤ)
  side : if negative then source.workHead ≤ 0 else 0 ≤ source.workHead

theorem IndexSnapshot.of_scan {length : ℕ} {source : Configuration M}
    {start ready : Configuration (virtualIndexCore M)} {position : ℤ}
    (snapshot : IndexSnapshot M length source start) (scan : IndexScanResult M start ready position) :
    IndexSnapshot M length source ready := by
  exact ⟨by rw [scan.memory]; exact snapshot.memory,
    scan.random.trans snapshot.random, scan.output.trans snapshot.output⟩

/-- Instruction fetching costs the distance to the origin, the virtual index
position, and two silent phase changes. It preserves all virtual tape contents. -/
theorem index_fetch (data : InputData Unit Bool) (bits : BitString) (length : ℕ)
    (source : Configuration M) (negative : Bool) (distance : ℕ)
    (position : source.workHead = signedPosition negative distance)
    (start : Configuration (virtualIndexCore M)) (related : IndexReady M length source negative start) :
    ∃ ready, IndexFetched M length source negative ready ∧
      (virtualIndexCore M).runFrom data bits start (distance + source.indexHead + 2) =
        (virtualIndexCore M).observe data bits ready := by
  let N := virtualIndexCore M
  let cache := source.work source.workHead
  let selected := N.stepConfiguration data start (indexControl M (.toOrigin source.state negative cache))
    none .stay .stay .stay .stay none
  have selectTable : N.transition start.state data.input[start.inputHead]?
      data.auxiliary[start.auxiliaryHead]?
      (if start.indexHead < data.index then some () else none) (start.work start.workHead) =
      .step (indexControl M (.toOrigin source.state negative cache)) none .stay .stay .stay .stay none := by
    have cell := related.memory source.workHead
    simp [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
      related.state, related.head, cell, virtualIndexCell, cache]
  have selectLive := N.observe_step data bits start _ _ _ _ _ _ _ selectTable
  have selectNext := N.next_step data bits start _ _ _ _ _ _ _ selectTable
  have selectRun : N.runFrom data bits start 1 = N.observe data bits selected :=
    N.runFrom_shift data bits start selected selectLive selectNext 0
  have selectedSnapshot : IndexSnapshot M length source selected :=
    ⟨related.memory, related.random, related.output⟩
  obtain ⟨atOrigin, originScan, originRun⟩ := index_scan_toOrigin M data bits selected source.state negative
    cache distance rfl (by simpa [selected, Machine.stepConfiguration, Move.onInt] using related.head.trans position)
    (fun i => by rw [selectedSnapshot.memory i]; rfl)
  have originSnapshot := selectedSnapshot.of_scan M originScan
  let entered := N.stepConfiguration data atOrigin (indexControl M (.toIndex source.state negative cache))
    none .stay .stay .stay .stay none
  have enterTable : N.transition atOrigin.state data.input[atOrigin.inputHead]?
      data.auxiliary[atOrigin.auxiliaryHead]?
      (if atOrigin.indexHead < data.index then some () else none) (atOrigin.work atOrigin.workHead) =
      .step (indexControl M (.toIndex source.state negative cache)) none .stay .stay .stay .stay none := by
    have cell := originSnapshot.memory 0
    simp [N, virtualIndexCore, Routine.machine, virtualIndexRoutine, virtualIndexTransition,
      originScan.state, selected, Machine.stepConfiguration, originScan.head, cell, virtualIndexCell]
  have enterLive := N.observe_step data bits atOrigin _ _ _ _ _ _ _ enterTable
  have enterNext := N.next_step data bits atOrigin _ _ _ _ _ _ _ enterTable
  have enterRun : N.runFrom data bits atOrigin 1 = N.observe data bits entered :=
    N.runFrom_shift data bits atOrigin entered enterLive enterNext 0
  have enteredSnapshot : IndexSnapshot M length source entered :=
    ⟨originSnapshot.memory, originSnapshot.random, originSnapshot.output⟩
  obtain ⟨ready, indexScan, indexRun⟩ := index_scan_toIndex M data bits entered source.state negative
    cache source.indexHead rfl (by simpa [entered, Machine.stepConfiguration, Move.onInt] using originScan.head)
    (fun i => by rw [enteredSnapshot.memory i]; simp [virtualIndexCell, eq_comm])
  have readySnapshot := enteredSnapshot.of_scan M indexScan
  refine ⟨ready, ⟨readySnapshot, indexScan.state, indexScan.head, related.side⟩, ?_⟩
  have clock : distance + source.indexHead + 2 = 1 + (distance + (1 + source.indexHead)) := by omega
  rw [clock, N.runFrom_add data bits start selected 1 selectRun,
    N.runFrom_add data bits selected atOrigin distance originRun,
    N.runFrom_add data bits atOrigin entered 1 enterRun]
  exact indexRun

def fetchedObservation (target : Configuration (virtualIndexCore M)) : RunState M → RunState (virtualIndexCore M)
  | .running _ => .running target
  | .halted result => .halted result

/-- At the fetched instruction, acceptance, rejection, exhaustion, and a live
source configuration have exactly their intended native observations. -/
theorem index_fetched_observe (data : InputData Unit Bool) (bits : BitString) (length : ℕ)
    (source : Configuration M) (negative : Bool) (target : Configuration (virtualIndexCore M))
    (related : IndexFetched M length source negative target) :
    (virtualIndexCore M).observe data bits target =
      fetchedObservation M target (M.observe (generatorData length) bits source) := by
  have cell := related.memory (source.indexHead : ℤ)
  simp only [Machine.observe, virtualIndexCore, Routine.machine, virtualIndexRoutine, related.state,
    Equiv.symm_apply_apply, virtualIndexTransition, related.head, cell, virtualIndexCell,
    generatorData, List.getElem?_nil]
  have less : ((source.indexHead : ℤ) < (length : ℤ)) ↔ source.indexHead < length := by omega
  simp only [Int.natCast_nonneg, true_and, less, decide_true, Bool.not_true,
    Bool.false_eq_true, ↓reduceIte, decide_eq_true_eq]
  cases instruction : M.transition source.state none none
      (if source.indexHead < length then some () else none) (source.work source.workHead) with
  | accept => simp [related.output, fetchedObservation]
  | reject => simp [fetchedObservation]
  | step state write work input auxiliary index emit => simp [fetchedObservation]
  | readRandom no yes =>
      by_cases available : source.randomHead < bits.length <;>
        simp [related.random, available, fetchedObservation]

end

end ComplexityOfGenerators.Simulation
