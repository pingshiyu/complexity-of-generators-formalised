import ComplexityOfGenerators.Simulation.ClockCarry

/-! One complete odometer tick, including both trips between the source work
head and the origin. A tick consumes no randomness and preserves the source
work tape, input positions, and output. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_tick (data : InputData I A) (bits : BitString) (length : ℕ)
    (work : ℤ → Option (Fin M.symbols)) (digits : List ℕ)
    (size : digits.length = p.degree) (bounded : ∀ d ∈ digits, d ≤ length)
    (action : ClockAction O M.states M.symbols) (negative : Bool)
    (remaining : Fin (p.coefficient + 1)) (distance : ℕ)
    (start : Configuration (polynomialClockCore M p))
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (memory : PolynomialClockMemory M p length work (clockLocations digits)
      (some (signedPosition negative distance)) start.work)
    (state : start.state = clockControl M p (.toOrigin action negative remaining))
    (head : start.workHead = signedPosition negative distance) :
    ∃ ticks ready, ticks ≤ 2 * distance + (p.degree + 1) * (2 * length + 5) + 2 ∧
      ready.state = clockControl M p (.execute action negative
        (clockNextBlock p remaining (clockDigitIncrement length digits).2)) ∧
      ready.workHead = signedPosition negative distance ∧
      PolynomialClockMemory M p length work (clockLocations (clockDigitIncrement length digits).1)
        (some (signedPosition negative distance)) ready.work ∧
      WorkFrame (polynomialClockCore M p) start ready ∧
      (polynomialClockCore M p).runFrom data bits start ticks =
        (polynomialClockCore M p).observe data bits ready := by
  let N := polynomialClockCore M p
  obtain ⟨origin, originScan, originRun⟩ := clock_scan_toOrigin M p data bits start action negative
    remaining distance bounds state head (fun i => by rw [memory i]; rfl)
  have originMemory : PolynomialClockMemory M p length work (clockLocations digits)
      (some (signedPosition negative distance)) origin.work := by rw [originScan.memory]; exact memory
  let entered := workStep N data origin
    (clockControl M p (.carry action negative remaining ⟨0, Nat.zero_lt_succ _⟩)) none .stay
  have enterRun : N.runFrom data bits origin 1 = N.observe data bits entered := by
    apply workStep_run
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
      originScan.state, state, originScan.head, originMemory 0, polynomialClockCell]
  have enterFrame : WorkFrame N origin entered := workStep_frame N data origin _ none .stay
    (originScan.readHeadBounds N bounds)
  have enteredMemory : PolynomialClockMemory M p length work (clockLocations ([] ++ digits))
      (some (signedPosition negative distance)) entered.work := originMemory
  obtain ⟨carryTime, returned, carryBound, returnState, returnHead, returnMemory, carryFrame, carryRun⟩ :=
    clock_carry M p data bits length work (some (signedPosition negative distance)) action negative remaining
      [] digits (by simpa using size) bounded entered
      (enterFrame.readHeadBounds N (originScan.readHeadBounds N bounds)) enteredMemory rfl originScan.head
  have returnBounds := carryFrame.readHeadBounds N
    (enterFrame.readHeadBounds N (originScan.readHeadBounds N bounds))
  obtain ⟨atWork, workScan, workRun⟩ := clock_scan_returnWork M p data bits returned action negative
    (clockNextBlock p remaining (clockDigitIncrement length digits).2) distance returnBounds returnState returnHead
    (fun i => by rw [returnMemory i]; simp [polynomialClockCell, eq_comm])
  have atMemory : PolynomialClockMemory M p length work (clockLocations (clockDigitIncrement length digits).1)
      (some (signedPosition negative distance)) atWork.work := by rw [workScan.memory]; exact returnMemory
  let ready := workStep N data atWork
    (clockControl M p (.execute action negative (clockNextBlock p remaining (clockDigitIncrement length digits).2)))
    none .stay
  have readyRun : N.runFrom data bits atWork 1 = N.observe data bits ready := by
    apply workStep_run
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
      workScan.state, returnState, workScan.head, atMemory _, polynomialClockCell]
  have readyFrame : WorkFrame N atWork ready := workStep_frame N data atWork _ none .stay
    (workScan.readHeadBounds N returnBounds)
  refine ⟨distance + (1 + (carryTime + (distance + 1))), ready, ?_, rfl, workScan.head, atMemory,
    (originScan.workFrame N).trans N (enterFrame.trans N
      (carryFrame.trans N ((workScan.workFrame N).trans N readyFrame))), ?_⟩
  · rw [size] at carryBound
    omega
  · rw [N.runFrom_add data bits start origin distance originRun,
      N.runFrom_add data bits origin entered 1 enterRun,
      N.runFrom_add data bits entered returned carryTime carryRun,
      N.runFrom_add data bits returned atWork distance workRun]
    exact readyRun

end

end ComplexityOfGenerators.Simulation
