import ComplexityOfGenerators.Simulation.ClockScans
import ComplexityOfGenerators.Simulation.WorkSteps

/-! One successful digit increment in the native polynomial clock. The
clearing, neighboring-cell write, and return scan are all charged explicitly. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_digit_step (data : InputData I A) (bits : BitString)
    (length position : ℕ) (small : position < length)
    (work : ℤ → Option (Fin M.symbols)) (digits : Fin p.degree → Option ℤ) (wh : Option ℤ)
    (digit : Fin p.degree) (digitPosition : digits digit = some (position : ℤ))
    (action : ClockAction O M.states M.symbols) (negative : Bool)
    (remaining : Fin (p.coefficient + 1))
    (start : Configuration (polynomialClockCore M p))
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (memory : PolynomialClockMemory M p length work digits wh start.work)
    (state : start.state = clockControl M p (.seek action negative remaining digit))
    (head : start.workHead = (position : ℤ)) :
    ∃ ready : Configuration (polynomialClockCore M p),
      ready.state = clockControl M p (.returnWork action negative remaining) ∧
      ready.workHead = 0 ∧
      PolynomialClockMemory M p length work
        (Function.update digits digit (some ((position + 1 : ℕ) : ℤ))) wh ready.work ∧
      WorkFrame (polynomialClockCore M p) start ready ∧
      (polynomialClockCore M p).runFrom data bits start (position + 4) =
        (polynomialClockCore M p).observe data bits ready := by
  let N := polynomialClockCore M p
  let cleared := workStep N data start (clockControl M p (.place action negative remaining digit))
    (some (clockWrite M p {clockRead M p (start.work start.workHead) with
      digit := Function.update (clockRead M p (start.work start.workHead)).digit digit false})) .right
  have clearRun : N.runFrom data bits start 1 = N.observe data bits cleared := by
    apply workStep_run
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
      state, head, memory _, polynomialClockCell, digitPosition, show position ≠ length by omega]
  have clearFrame : WorkFrame N start cleared := workStep_frame N data start _ _ .right bounds
  have clearedHead : cleared.workHead = ((position + 1 : ℕ) : ℤ) := by
    simp [cleared, workStep, Machine.stepConfiguration, Move.onInt, head]
  have clearedMemory : PolynomialClockMemory M p length work (Function.update digits digit none) wh
      cleared.work := by
    simpa only [cleared, workStep, Machine.stepConfiguration, head] using
      memory.clear_digit M p digit position digitPosition
  let placed := workStep N data cleared (clockControl M p (.back action negative remaining))
    (some (clockWrite M p {clockRead M p (cleared.work cleared.workHead) with
      digit := Function.update (clockRead M p (cleared.work cleared.workHead)).digit digit true})) .stay
  have placeRun : N.runFrom data bits cleared 1 = N.observe data bits placed := by
    apply workStep_run
    simp only [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, cleared,
      workStep, Machine.stepConfiguration, Equiv.symm_apply_apply, clockTransition]
  have placeFrame : WorkFrame N cleared placed :=
    workStep_frame N data cleared _ _ .stay (clearFrame.readHeadBounds N bounds)
  have placedHead : placed.workHead = ((position + 1 : ℕ) : ℤ) := clearedHead
  have placedMemory : PolynomialClockMemory M p length work
      (Function.update digits digit (some ((position + 1 : ℕ) : ℤ))) wh placed.work := by
    have result := clearedMemory.place_digit M p digit ((position + 1 : ℕ) : ℤ) (by simp)
    simpa only [placed, workStep, Machine.stepConfiguration, clearedHead, Function.update_idem] using result
  obtain ⟨origin, scan, scanRun⟩ := clock_scan_left M p data bits placed
    (.back action negative remaining) (position + 1)
    (placeFrame.readHeadBounds N (clearFrame.readHeadBounds N bounds)) rfl placedHead
    (fun raw ho input auxiliary index => by simp [clockTransition, ho])
    (fun i => by rw [placedMemory i]; rfl)
  have originMemory : PolynomialClockMemory M p length work
      (Function.update digits digit (some ((position + 1 : ℕ) : ℤ))) wh origin.work := by
    rw [scan.memory]; exact placedMemory
  let ready := workStep N data origin (clockControl M p (.returnWork action negative remaining)) none .stay
  have readyRun : N.runFrom data bits origin 1 = N.observe data bits ready := by
    apply workStep_run
    simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
      scan.state, placed, workStep, Machine.stepConfiguration, scan.head, originMemory 0, polynomialClockCell]
  have readyFrame : WorkFrame N origin ready := workStep_frame N data origin _ none .stay
    (scan.readHeadBounds N (placeFrame.readHeadBounds N (clearFrame.readHeadBounds N bounds)))
  refine ⟨ready, rfl, scan.head, originMemory,
    clearFrame.trans N (placeFrame.trans N (scan.workFrame N |>.trans N readyFrame)), ?_⟩
  have time : position + 4 = 1 + (1 + ((position + 1) + 1)) := by omega
  rw [time, N.runFrom_add data bits start cleared 1 clearRun,
    N.runFrom_add data bits cleared placed 1 placeRun,
    N.runFrom_add data bits placed origin (position + 1) scanRun]
  exact readyRun

end

end ComplexityOfGenerators.Simulation
