import ComplexityOfGenerators.Simulation.PolynomialClockMemory
import ComplexityOfGenerators.Simulation.VirtualIndexScan

/-! Read-only scans used by the polynomial clock. The conclusions retain all
three source read-only head positions, not just the work tape and output. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_scan_toOrigin (data : InputData I A) (bits : BitString)
    (start : Configuration (polynomialClockCore M p))
    (action : ClockAction O M.states M.symbols) (negative : Bool)
    (remaining : Fin (p.coefficient + 1)) (distance : ℕ)
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (state : start.state = clockControl M p (.toOrigin action negative remaining))
    (head : start.workHead = signedPosition negative distance)
    (origin : ∀ i, (clockRead M p (start.work i)).origin = decide (i = 0)) :
    ∃ ready, ScanResult (polynomialClockCore M p) start ready 0 ∧
      (polynomialClockCore M p).runFrom data bits start distance =
        (polynomialClockCore M p).observe data bits ready := by
  obtain ⟨ready, scan, execution⟩ :=
    tapeScan_with_heads (polynomialClockCore M p) data bits start
      (clockControl M p (.toOrigin action negative remaining))
      (fun k => signedPosition negative (distance - k))
      (fun _ => if negative then .right else .left) distance bounds state (by simpa using head)
      (fun k hk => by
        rw [signedPosition_in negative _ (by omega)]
        congr 1)
      (fun k hk input auxiliary index => by
        have notOrigin := signedPosition_ne_zero negative (show 0 < distance - k by omega)
        simp [polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
          origin, notOrigin])
  exact ⟨ready, by simpa using scan, execution⟩

theorem clock_scan_seek (data : InputData I A) (bits : BitString)
    (start : Configuration (polynomialClockCore M p))
    (action : ClockAction O M.states M.symbols) (negative : Bool)
    (remaining : Fin (p.coefficient + 1)) (digit : Fin p.degree) (position : ℕ)
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (state : start.state = clockControl M p (.seek action negative remaining digit))
    (head : start.workHead = 0)
    (marker : ∀ i, (clockRead M p (start.work i)).digit digit = decide (i = (position : ℤ))) :
    ∃ ready, ScanResult (polynomialClockCore M p) start ready position ∧
      (polynomialClockCore M p).runFrom data bits start position =
        (polynomialClockCore M p).observe data bits ready := by
  exact tapeScan_with_heads (polynomialClockCore M p) data bits start
    (clockControl M p (.seek action negative remaining digit))
    (fun k => (k : ℤ)) (fun _ => .right) position bounds state head
    (fun k _ => by simp [Move.onInt])
    (fun k hk input auxiliary index => by
      have different : (k : ℤ) ≠ (position : ℤ) := by omega
      simp [polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
        marker, different])

theorem clock_scan_left (data : InputData I A) (bits : BitString)
    (start : Configuration (polynomialClockCore M p))
    (phase : ClockPhase O M.states M.symbols p.coefficient p.degree) (distance : ℕ)
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (state : start.state = clockControl M p phase)
    (head : start.workHead = (distance : ℤ))
    (table : ∀ raw, (clockRead M p raw).origin = false → ∀ input auxiliary index,
      clockTransition M p phase input auxiliary index raw =
        .step (clockControl M p phase) none .left .stay .stay .stay none)
    (origin : ∀ i, (clockRead M p (start.work i)).origin = decide (i = 0)) :
    ∃ ready, ScanResult (polynomialClockCore M p) start ready 0 ∧
      (polynomialClockCore M p).runFrom data bits start distance =
        (polynomialClockCore M p).observe data bits ready := by
  obtain ⟨ready, scan, execution⟩ :=
    tapeScan_with_heads (polynomialClockCore M p) data bits start (clockControl M p phase)
      (fun k => ((distance - k : ℕ) : ℤ)) (fun _ => .left) distance bounds state (by simpa using head)
      (fun k hk => by simp only [Move.onInt]; omega)
      (fun k hk input auxiliary index => by
        change clockTransition M p ((clockControl M p).symm (clockControl M p phase)) _ _ _ _ = _
        rw [Equiv.symm_apply_apply]
        exact table _ (by rw [origin]; simp; omega) _ _ _)
  exact ⟨ready, by simpa using scan, execution⟩

theorem clock_scan_returnWork (data : InputData I A) (bits : BitString)
    (start : Configuration (polynomialClockCore M p))
    (action : ClockAction O M.states M.symbols) (negative : Bool)
    (remaining : Fin (p.coefficient + 1)) (distance : ℕ)
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (state : start.state = clockControl M p (.returnWork action negative remaining))
    (head : start.workHead = 0)
    (marker : ∀ i, (clockRead M p (start.work i)).workHead =
      decide (i = signedPosition negative distance)) :
    ∃ ready, ScanResult (polynomialClockCore M p) start ready (signedPosition negative distance) ∧
      (polynomialClockCore M p).runFrom data bits start distance =
        (polynomialClockCore M p).observe data bits ready := by
  exact tapeScan_with_heads (polynomialClockCore M p) data bits start
    (clockControl M p (.returnWork action negative remaining))
    (signedPosition negative) (fun _ => if negative then .left else .right) distance bounds state
    (by simp [head]) (fun k _ => signedPosition_out negative k)
    (fun k hk input auxiliary index => by
      have different : signedPosition negative k ≠ signedPosition negative distance := by
        cases negative <;> simp [signedPosition] <;> omega
      simp [polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
        marker, different])

end

end ComplexityOfGenerators.Simulation
