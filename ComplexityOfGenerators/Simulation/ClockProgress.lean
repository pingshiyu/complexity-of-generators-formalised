import ComplexityOfGenerators.Simulation.ClockExecute

/-! Progress of the clocked source simulation. At the deadline a pending
nonhalting instruction is rejected; an acceptance already reached at that
deadline is retained. Exhaustion remains a nonaccepting outcome. -/

namespace ComplexityOfGenerators

def Outcome.acceptedWord {O : Type} : Outcome O → Option (List O)
  | .accepted w => some w
  | .rejected | .exhausted => none

def RunState.acceptedWord {I A O : Type} {M : Machine I A O} : RunState M → Option (List O)
  | .halted outcome => outcome.acceptedWord
  | .running _ => none

namespace Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_simulates_next (data : InputData I A) (bits : BitString) (length : ℕ)
    (digits : List ℕ) (size : digits.length = p.degree) (bounded : ∀ d ∈ digits, d ≤ length)
    (remaining : Fin (p.coefficient + 1)) (positive : 0 < remaining.val)
    (source nextSource : Configuration M) (negative : Bool) (target : Configuration (polynomialClockCore M p))
    (related : ClockReady M p length digits remaining source negative target)
    (bounds : ReadHeadBounds M data source) (step : M.next data bits source = .running nextSource) :
    ∃ ticks ready newNegative,
      ticks ≤ 2 * source.workHead.natAbs + (p.degree + 1) * (2 * length + 5) + 5 ∧
      ClockReady M p length (clockDigitIncrement length digits).1
        (clockNextBlock p remaining (clockDigitIncrement length digits).2) nextSource newNegative ready ∧
      (polynomialClockCore M p).runFrom data bits target ticks =
        (polynomialClockCore M p).observe data bits ready := by
  let N := polynomialClockCore M p
  cases instruction : M.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead < data.index then some true else none) (source.work source.workHead) with
  | accept => simp [Machine.next, instruction] at step
  | reject => simp [Machine.next, instruction] at step
  | step next write work input auxiliary index emit =>
      have native := M.next_step data bits source next write work input auxiliary index emit instruction
      have same := RunState.running.inj (step.symm.trans native)
      subst nextSource
      obtain ⟨ticks, executing, time, state, head, snapshot, execution⟩ :=
        clock_suspend M p data bits length digits size bounded remaining positive source negative target related bounds
          (.step next write work input auxiliary index emit) instruction
      obtain ⟨ready, readyRelated, readyRun⟩ := clock_execute_step M p data bits length _ _ source negative
        related.side executing snapshot bounds next write work input auxiliary index emit state head
      refine ⟨ticks + 2, ready, clockSide source.workHead negative work, by omega, readyRelated, ?_⟩
      rw [N.runFrom_add data bits target executing ticks execution]
      exact readyRun
  | readRandom no yes =>
      cases read : bits[source.randomHead]? with
      | none => simp [Machine.next, instruction, read] at step
      | some bit =>
          have same : {source with state := if bit then yes else no, randomHead := source.randomHead + 1} = nextSource := by
            simpa [Machine.next, instruction, read] using step
          subst nextSource
          obtain ⟨ticks, executing, time, state, head, snapshot, execution⟩ :=
            clock_suspend M p data bits length digits size bounded remaining positive source negative target related bounds
              (.random no yes) instruction
          obtain ⟨ready, readyRelated, readyRun⟩ := clock_execute_random M p data bits length _ _ source negative
            related.side executing snapshot no yes bit state head read
          refine ⟨ticks + 1, ready, negative, by omega, readyRelated, ?_⟩
          rw [N.runFrom_add data bits target executing ticks execution]
          exact readyRun

theorem clock_expired (data : InputData I A) (bits : BitString) (length : ℕ) (digits : List ℕ)
    (remaining : Fin (p.coefficient + 1)) (zero : remaining.val = 0)
    (source : Configuration M) (negative : Bool) (target : Configuration (polynomialClockCore M p))
    (related : ClockReady M p length digits remaining source negative target) :
    ∃ result, (polynomialClockCore M p).observe data bits target = .halted result ∧
      result.acceptedWord = (M.observe data bits source).acceptedWord := by
  have readCell := related.memory source.workHead
  cases instruction : M.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead < data.index then some true else none) (source.work source.workHead) with
  | accept =>
      refine ⟨.accepted source.output, ?_, ?_⟩
      · simp [Machine.observe, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
          related.state, related.head, related.input, related.auxiliary, related.index, related.output,
          readCell, polynomialClockCell, instruction]
      · simp [Machine.observe, instruction, RunState.acceptedWord]
  | reject =>
      refine ⟨.rejected, ?_, ?_⟩
      · simp [Machine.observe, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
          related.state, related.head, related.input, related.auxiliary, related.index,
          readCell, polynomialClockCell, instruction]
      · simp [Machine.observe, instruction, RunState.acceptedWord]
  | step next write work input auxiliary index emit =>
      refine ⟨.rejected, ?_, ?_⟩
      · simp [Machine.observe, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
          related.state, related.head, related.input, related.auxiliary, related.index,
          readCell, polynomialClockCell, instruction, zero]
      · simp [Machine.observe, instruction, RunState.acceptedWord, Outcome.acceptedWord]
  | readRandom no yes =>
      refine ⟨.rejected, ?_, ?_⟩
      · simp [Machine.observe, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
          related.state, related.head, related.input, related.auxiliary, related.index,
          readCell, polynomialClockCell, instruction, zero]
      · simp only [Machine.observe, instruction]
        split <;> rfl

theorem clock_simulates_halted (data : InputData I A) (bits : BitString) (length : ℕ)
    (digits : List ℕ) (size : digits.length = p.degree) (bounded : ∀ d ∈ digits, d ≤ length)
    (remaining : Fin (p.coefficient + 1)) (positive : 0 < remaining.val)
    (source : Configuration M) (negative : Bool) (target : Configuration (polynomialClockCore M p))
    (related : ClockReady M p length digits remaining source negative target)
    (bounds : ReadHeadBounds M data source) (result : Outcome O)
    (halted : M.observe data bits source = .halted result) :
    ∃ ticks, ticks ≤ 2 * source.workHead.natAbs + (p.degree + 1) * (2 * length + 5) + 3 ∧
      (polynomialClockCore M p).runFrom data bits target ticks = .halted result := by
  have readCell := related.memory source.workHead
  cases instruction : M.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead < data.index then some true else none) (source.work source.workHead) with
  | accept =>
      have same : result = .accepted source.output := by simpa [Machine.observe, instruction] using halted.symm
      subst result
      refine ⟨0, by omega, ?_⟩
      simp [Machine.runFrom, Machine.observe, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
        related.state, related.head, related.input, related.auxiliary, related.index, related.output,
        readCell, polynomialClockCell, instruction]
  | reject =>
      have same : result = .rejected := by simpa [Machine.observe, instruction] using halted.symm
      subst result
      refine ⟨0, by omega, ?_⟩
      simp [Machine.runFrom, Machine.observe, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
        related.state, related.head, related.input, related.auxiliary, related.index,
        readCell, polynomialClockCell, instruction]
  | step next write work input auxiliary index emit => simp [Machine.observe, instruction] at halted
  | readRandom no yes =>
      have unavailable : ¬ source.randomHead < bits.length := by
        intro available
        simp [Machine.observe, instruction, available] at halted
      have same : result = .exhausted := by simpa [Machine.observe, instruction, unavailable] using halted.symm
      subst result
      obtain ⟨ticks, executing, time, state, head, snapshot, execution⟩ :=
        clock_suspend M p data bits length digits size bounded remaining positive source negative target related bounds
          (.random no yes) instruction
      refine ⟨ticks, time, ?_⟩
      rw [execution]
      simp [Machine.observe, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
        state, snapshot.random, unavailable]

end

end Simulation
end ComplexityOfGenerators
