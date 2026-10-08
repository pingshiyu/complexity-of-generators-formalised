import ComplexityOfGenerators.Simulation.ClockDigitStep

/-! A digit at its last unary position is reset to the origin, then control
passes to the next digit. This also covers radix one (empty physical input). -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_digit_reset (data : InputData I A) (bits : BitString) (length : ℕ)
    (work : ℤ → Option (Fin M.symbols)) (digits : Fin p.degree → Option ℤ) (wh : Option ℤ)
    (digit : Fin p.degree) (digitPosition : digits digit = some (length : ℤ))
    (action : ClockAction O M.states M.symbols) (negative : Bool)
    (remaining : Fin (p.coefficient + 1))
    (start : Configuration (polynomialClockCore M p))
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (memory : PolynomialClockMemory M p length work digits wh start.work)
    (state : start.state = clockControl M p (.seek action negative remaining digit))
    (head : start.workHead = (length : ℤ)) :
    ∃ ready : Configuration (polynomialClockCore M p),
      ready.state = clockControl M p (.carry action negative remaining ⟨digit.val + 1, by omega⟩) ∧
      ready.workHead = 0 ∧
      PolynomialClockMemory M p length work (Function.update digits digit (some 0)) wh ready.work ∧
      WorkFrame (polynomialClockCore M p) start ready ∧
      (polynomialClockCore M p).runFrom data bits start (length + 2) =
        (polynomialClockCore M p).observe data bits ready := by
  let N := polynomialClockCore M p
  let cleared := workStep N data start (clockControl M p (.reset action negative remaining digit))
    (some (clockWrite M p {clockRead M p (start.work start.workHead) with
      digit := Function.update (clockRead M p (start.work start.workHead)).digit digit false})) .stay
  have clearRun : N.runFrom data bits start 1 = N.observe data bits cleared := by
    apply workStep_run
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
      state, head, memory _, polynomialClockCell, digitPosition]
  have clearFrame : WorkFrame N start cleared := workStep_frame N data start _ _ .stay bounds
  have clearedHead : cleared.workHead = (length : ℤ) := head
  have clearedMemory : PolynomialClockMemory M p length work (Function.update digits digit none) wh
      cleared.work := by
    simpa only [cleared, workStep, Machine.stepConfiguration, head] using
      memory.clear_digit M p digit length digitPosition
  obtain ⟨origin, scan, scanRun⟩ := clock_scan_left M p data bits cleared
    (.reset action negative remaining digit) length
    (clearFrame.readHeadBounds N bounds) rfl clearedHead
    (fun raw ho input auxiliary index => by simp [clockTransition, ho])
    (fun i => by rw [clearedMemory i]; rfl)
  have originMemory : PolynomialClockMemory M p length work (Function.update digits digit none) wh
      origin.work := by
    rw [scan.memory]; exact clearedMemory
  let ready := workStep N data origin
    (clockControl M p (.carry action negative remaining ⟨digit.val + 1, by omega⟩))
    (some (clockWrite M p {clockRead M p (origin.work origin.workHead) with
      digit := Function.update (clockRead M p (origin.work origin.workHead)).digit digit true})) .stay
  have readyRun : N.runFrom data bits origin 1 = N.observe data bits ready := by
    apply workStep_run
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
      scan.state, cleared, workStep, Machine.stepConfiguration, scan.head, originMemory 0, polynomialClockCell]
  have readyFrame : WorkFrame N origin ready := workStep_frame N data origin _ _ .stay
    (scan.readHeadBounds N (clearFrame.readHeadBounds N bounds))
  have readyMemory : PolynomialClockMemory M p length work (Function.update digits digit (some 0)) wh
      ready.work := by
    have result := originMemory.place_digit M p digit 0 (by simp)
    simpa only [ready, workStep, Machine.stepConfiguration, scan.head, Function.update_idem] using result
  refine ⟨ready, rfl, scan.head, readyMemory,
    clearFrame.trans N (scan.workFrame N |>.trans N readyFrame), ?_⟩
  have time : length + 2 = 1 + (length + 1) := by omega
  rw [time, N.runFrom_add data bits start cleared 1 clearRun,
    N.runFrom_add data bits cleared origin length scanRun]
  exact readyRun

end

end ComplexityOfGenerators.Simulation
