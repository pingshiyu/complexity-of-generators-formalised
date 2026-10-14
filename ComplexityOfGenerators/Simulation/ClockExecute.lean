import ComplexityOfGenerators.Simulation.ClockSuspend

/-! Executing the source instruction after a native clock tick. Source work,
input, index, and output effects are preserved, and random instructions consume
exactly one original choice bit. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

def clockSide (head : ℤ) (negative : Bool) (move : Move) : Bool :=
  if head = 0 then decide (move = .left) else negative

theorem clockSide_correct (head : ℤ) (negative : Bool) (move : Move)
    (side : if negative then head ≤ 0 else 0 ≤ head) :
    if clockSide head negative move then move.onInt head ≤ 0 else 0 ≤ move.onInt head := by
  cases negative <;> cases move <;> simp_all [clockSide, Move.onInt] <;> omega

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_execute_step (data : InputData I A) (bits : BitString) (length : ℕ) (digits : List ℕ)
    (remaining : Fin (p.coefficient + 1)) (source : Configuration M) (negative : Bool)
    (side : if negative then source.workHead ≤ 0 else 0 ≤ source.workHead)
    (target : Configuration (polynomialClockCore M p))
    (related : ClockSnapshot M p length digits source target) (bounds : ReadHeadBounds M data source)
    (next : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (state : target.state = clockControl M p
      (.execute (.step next write work input auxiliary index emit) negative remaining))
    (head : target.workHead = source.workHead) :
    ∃ ready, ClockReady M p length digits remaining
        (M.stepConfiguration data source next write work input auxiliary index emit)
        (clockSide source.workHead negative work) ready ∧
      (polynomialClockCore M p).runFrom data bits target 2 =
        (polynomialClockCore M p).observe data bits ready := by
  let N := polynomialClockCore M p
  let nextSide := clockSide source.workHead negative work
  let value := match write with | none => source.work source.workHead | some a => some a
  let written := N.stepConfiguration data target (clockControl M p (.placeWork next nextSide remaining))
    (some (clockWrite M p {clockRead M p (target.work target.workHead) with
      source := value, workHead := false})) work input auxiliary index emit
  have table : N.transition target.state data.input[target.inputHead]? data.auxiliary[target.auxiliaryHead]?
      (if target.indexHead < data.index then some () else none) (target.work target.workHead) =
      .step (clockControl M p (.placeWork next nextSide remaining))
        (some (clockWrite M p {clockRead M p (target.work target.workHead) with
          source := value, workHead := false})) work input auxiliary index emit := by
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition, state,
      head, related.memory _, polynomialClockCell, value, nextSide, clockSide]
    rfl
  have writtenRun : N.runFrom data bits target 1 = N.observe data bits written :=
    N.runFrom_shift data bits target written (N.observe_step data bits target _ _ _ _ _ _ _ table)
      (N.next_step data bits target _ _ _ _ _ _ _ table) 0
  have writtenHead : written.workHead = work.onInt source.workHead := by
    change work.onInt target.workHead = _
    rw [head]
  have writtenMemory : PolynomialClockMemory M p length (Function.update source.work source.workHead value)
      (clockLocations digits) none written.work := by
    simpa only [written, Machine.stepConfiguration, head] using related.memory.write_source M p source.workHead value
  let ready := workStep N data written (clockControl M p (.source next nextSide remaining))
    (some (clockWrite M p {clockRead M p (written.work written.workHead) with workHead := true})) .stay
  have readyRun : N.runFrom data bits written 1 = N.observe data bits ready := by
    apply workStep_run
    simp only [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, written,
      Machine.stepConfiguration, Equiv.symm_apply_apply, clockTransition]
  have writtenBounds : ReadHeadBounds N data written := ReadHeadBounds.stepConfiguration N data target _ _
    work input auxiliary index emit (related.readHeadBounds M p bounds)
  have frame : WorkFrame N written ready := workStep_frame N data written _ _ .stay writtenBounds
  have readyMemory : PolynomialClockMemory M p length (Function.update source.work source.workHead value)
      (clockLocations digits) (some (work.onInt source.workHead)) ready.work := by
    simpa only [ready, workStep, Machine.stepConfiguration, writtenHead] using
      writtenMemory.place_work M p (work.onInt source.workHead)
  refine ⟨ready, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, rfl, writtenHead, clockSide_correct _ _ _ side⟩, ?_⟩
  · cases write <;> simpa [Machine.stepConfiguration, value] using readyMemory
  · exact frame.random.trans related.random
  · rw [frame.output]
    cases emit <;> simp [written, Machine.stepConfiguration, related.output]
  · rw [frame.input]
    change input.onInput _ target.inputHead = input.onInput _ source.inputHead
    rw [related.input]
  · rw [frame.auxiliary]
    change auxiliary.onInput _ target.auxiliaryHead = auxiliary.onInput _ source.auxiliaryHead
    rw [related.auxiliary]
  · rw [frame.index]
    change index.onInput _ target.indexHead = index.onInput _ source.indexHead
    rw [related.index]
  · exact (N.runFrom_add data bits target written 1 writtenRun 1).trans readyRun

theorem clock_execute_random (data : InputData I A) (bits : BitString) (length : ℕ) (digits : List ℕ)
    (remaining : Fin (p.coefficient + 1)) (source : Configuration M) (negative : Bool)
    (side : if negative then source.workHead ≤ 0 else 0 ≤ source.workHead)
    (target : Configuration (polynomialClockCore M p))
    (related : ClockSnapshot M p length digits source target)
    (no yes : Fin M.states) (bit : Bool)
    (state : target.state = clockControl M p (.execute (.random no yes) negative remaining))
    (head : target.workHead = source.workHead) (read : bits[source.randomHead]? = some bit) :
    ∃ ready, ClockReady M p length digits remaining
        {source with state := if bit then yes else no, randomHead := source.randomHead + 1} negative ready ∧
      (polynomialClockCore M p).runFrom data bits target 1 =
        (polynomialClockCore M p).observe data bits ready := by
  let N := polynomialClockCore M p
  let ready : Configuration N := {target with
    state := clockControl M p (.source (if bit then yes else no) negative remaining)
    randomHead := target.randomHead + 1}
  have table : N.transition target.state data.input[target.inputHead]? data.auxiliary[target.auxiliaryHead]?
      (if target.indexHead < data.index then some () else none) (target.work target.workHead) =
      .readRandom (clockControl M p (.source no negative remaining))
        (clockControl M p (.source yes negative remaining)) := by
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition, state]
  have available : source.randomHead < bits.length := by
    by_contra unavailable
    rw [List.getElem?_eq_none (by omega)] at read
    cases read
  have live : N.observe data bits target = .running target := by
    simp [Machine.observe, table, related.random, available]
  have next : N.next data bits target = .running ready := by
    simp only [Machine.next, table, related.random, read]
    cases bit <;> simp [ready, related.random]
  exact ⟨ready, ⟨⟨related.memory, congrArg (· + 1) related.random, related.output,
    related.input, related.auxiliary, related.index⟩, rfl, head, side⟩,
    N.runFrom_shift data bits target ready live next 0⟩

end

end ComplexityOfGenerators.Simulation
