import ComplexityOfGenerators.Simulation.ClockDigitReset
import ComplexityOfGenerators.Simulation.ClockArithmetic

/-! Complete execution of the native odometer carry. This connects the digit
arithmetic to the transition table, with a linear bound per digit. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

def clockNextBlock (p : PolynomialBound) (remaining : Fin (p.coefficient + 1)) (carry : Bool) :
    Fin (p.coefficient + 1) :=
  ⟨if carry then remaining.val - 1 else remaining.val, by split <;> omega⟩

@[simp] theorem clockNextBlock_false (p : PolynomialBound) (remaining : Fin (p.coefficient + 1)) :
    clockNextBlock p remaining false = remaining := Fin.ext rfl

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_carry (data : InputData I A) (bits : BitString) (length : ℕ)
    (work : ℤ → Option (Fin M.symbols)) (wh : Option ℤ)
    (action : ClockAction O M.states M.symbols) (negative : Bool)
    (remaining : Fin (p.coefficient + 1)) (pre suffix : List ℕ)
    (size : pre.length + suffix.length = p.degree)
    (bounded : ∀ d ∈ suffix, d ≤ length)
    (start : Configuration (polynomialClockCore M p))
    (bounds : ReadHeadBounds (polynomialClockCore M p) data start)
    (memory : PolynomialClockMemory M p length work (clockLocations (pre ++ suffix)) wh start.work)
    (state : start.state = clockControl M p (.carry action negative remaining ⟨pre.length, by omega⟩))
    (head : start.workHead = 0) :
    ∃ ticks ready, ticks ≤ (suffix.length + 1) * (2 * length + 5) ∧
      ready.state = clockControl M p (.returnWork action negative
        (clockNextBlock p remaining (clockDigitIncrement length suffix).2)) ∧
      ready.workHead = 0 ∧
      PolynomialClockMemory M p length work
        (clockLocations (pre ++ (clockDigitIncrement length suffix).1)) wh ready.work ∧
      WorkFrame (polynomialClockCore M p) start ready ∧
      (polynomialClockCore M p).runFrom data bits start ticks =
        (polynomialClockCore M p).observe data bits ready := by
  induction suffix generalizing pre start with
  | nil =>
      let N := polynomialClockCore M p
      let ready := workStep N data start
        (clockControl M p (.returnWork action negative (clockNextBlock p remaining true))) none .stay
      have run : N.runFrom data bits start 1 = N.observe data bits ready := by
        apply workStep_run
        have atEnd : ¬ pre.length < p.degree := by simp only [List.length_nil, Nat.add_zero] at size; omega
        simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
          state, atEnd, clockNextBlock]
      refine ⟨1, ready, by simp, rfl, head, memory,
        workStep_frame N data start _ none .stay bounds, run⟩
  | cons d suffix ih =>
      let N := polynomialClockCore M p
      have digitBound : pre.length < p.degree := by simp only [List.length_cons] at size; omega
      let digit : Fin p.degree := ⟨pre.length, digitBound⟩
      let entered := workStep N data start
        (clockControl M p (.seek action negative remaining digit)) none .stay
      have enterRun : N.runFrom data bits start 1 = N.observe data bits entered := by
        apply workStep_run
        simp [N, polynomialClockCore, Routine.machine, polynomialClockRoutine, clockTransition,
          state, digitBound, digit]
      have enterFrame : WorkFrame N start entered := workStep_frame N data start _ none .stay bounds
      have enteredMemory : PolynomialClockMemory M p length work (clockLocations (pre ++ d :: suffix)) wh
          entered.work := memory
      have position : clockLocations (pre ++ d :: suffix) digit = some (d : ℤ) :=
        clockLocations_at pre suffix d digitBound
      obtain ⟨atDigit, scan, scanRun⟩ := clock_scan_seek M p data bits entered action negative remaining digit d
        (enterFrame.readHeadBounds N bounds) rfl head
        (fun i => by rw [enteredMemory i]; simp [polynomialClockCell, position, eq_comm])
      have atMemory : PolynomialClockMemory M p length work (clockLocations (pre ++ d :: suffix)) wh
          atDigit.work := by rw [scan.memory]; exact enteredMemory
      have atBounds := scan.readHeadBounds N (enterFrame.readHeadBounds N bounds)
      have atState : atDigit.state = clockControl M p (.seek action negative remaining digit) := scan.state
      have atFrame := enterFrame.trans N (scan.workFrame N)
      by_cases small : d < length
      · obtain ⟨ready, readyState, readyHead, readyMemory, readyFrame, readyRun⟩ :=
          clock_digit_step M p data bits length d small work _ wh digit position action negative remaining
            atDigit atBounds atMemory atState scan.head
        have updated : PolynomialClockMemory M p length work
            (clockLocations (pre ++ (d + 1) :: suffix)) wh ready.work := by
          rw [clockLocations_update pre suffix d (d + 1) digitBound]
          exact readyMemory
        refine ⟨1 + (d + (d + 4)), ready, ?_, ?_, readyHead, ?_, atFrame.trans N readyFrame, ?_⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa only [clockDigitIncrement, small, ↓reduceIte, clockNextBlock_false] using readyState
        · simpa only [clockDigitIncrement, small, ↓reduceIte] using updated
        · rw [N.runFrom_add data bits start entered 1 enterRun,
            N.runFrom_add data bits entered atDigit d scanRun]
          exact readyRun
      · have last : d = length := by have := bounded d (by simp); omega
        subst d
        obtain ⟨reset, resetState, resetHead, resetMemory, resetFrame, resetRun⟩ :=
          clock_digit_reset M p data bits length work _ wh digit position action negative remaining
            atDigit atBounds atMemory atState scan.head
        have updated : PolynomialClockMemory M p length work
            (clockLocations ((pre ++ [0]) ++ suffix)) wh reset.work := by
          rw [List.append_assoc]
          change PolynomialClockMemory M p length work (clockLocations (pre ++ 0 :: suffix)) wh reset.work
          rw [clockLocations_update pre suffix length 0 digitBound]
          exact resetMemory
        have resetState' : reset.state = clockControl M p
            (.carry action negative remaining ⟨(pre ++ [0]).length, by simp; omega⟩) := by
          simpa only [List.length_append, List.length_singleton, digit] using resetState
        obtain ⟨tailTime, ready, tailBound, readyState, readyHead, readyMemory, readyFrame, readyRun⟩ :=
          ih (pre ++ [0]) (by simpa only [List.length_append, List.length_singleton, List.length_cons,
            List.length_nil, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using size)
            (fun x hx => bounded x (List.mem_cons_of_mem _ hx)) reset
            (resetFrame.readHeadBounds N atBounds) updated resetState' resetHead
        refine ⟨1 + (length + ((length + 2) + tailTime)), ready, ?_, ?_, readyHead, ?_,
          atFrame.trans N (resetFrame.trans N readyFrame), ?_⟩
        · simp only [List.length_cons]
          nlinarith
        · simpa only [clockDigitIncrement, lt_self_iff_false, ↓reduceIte] using readyState
        · simpa only [clockDigitIncrement, lt_self_iff_false, ↓reduceIte, List.append_assoc,
            List.cons_append, List.nil_append] using readyMemory
        · rw [N.runFrom_add data bits start entered 1 enterRun,
            N.runFrom_add data bits entered atDigit length scanRun,
            N.runFrom_add data bits atDigit reset (length + 2) resetRun]
          exact readyRun

end

end ComplexityOfGenerators.Simulation
