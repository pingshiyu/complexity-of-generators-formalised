import ComplexityOfGenerators.Simulation.TransducerBank.Execution

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- Scan a nonnegative virtual head back to its origin, then transfer control.
The transition-table hypothesis is finite and purely local to this routine. -/
theorem rewind_steps (data : InputData I A) (bits : BitString) (state finish : Q) (j : Fin k)
    (selected : B.select state = j)
    (table : ∀ input auxiliary index origin cell,
      B.transition state input auxiliary index origin cell =
        .step (if origin then finish else state) cell (if origin then .stay else .left) .stay .stay .stay none)
    (position : ℕ) (c : BankConfiguration O Q S k) (atState : c.state = state) (atHead : c.head j = position)
    (input : c.inputHead ≤ data.input.length) (auxiliary : c.auxiliaryHead ≤ data.auxiliary.length)
    (index : c.indexHead ≤ data.index) :
    B.Steps data bits c (position + 1) {c with state := finish, head := Function.update c.head j 0} := by
  induction position generalizing c with
  | zero =>
      have go : B.Steps data bits c 1 {c with state := finish} := by
        apply Steps.go B data bits c finish input auxiliary index
        simp [instruction, atState, selected, atHead, table]
      have heads : Function.update c.head j 0 = c.head := by
        change c.head j = 0 at atHead
        rw [← atHead]
        exact Function.update_eq_self _ _
      simpa only [heads] using go
  | succ position ih =>
      let d : BankConfiguration O Q S k := {c with head := Function.update c.head j (position : ℤ)}
      have step : B.Steps data bits c 1 d := by
        have instruction : B.instruction data c = .step state (c.tape j (c.head j)) .left .stay .stay .stay none := by
          simp [TapeBank.instruction, atState, selected, atHead, table]
          omega
        have one := Steps.single B data bits c state (c.tape j (c.head j)) .left .stay .stay .stay none instruction
        have symbol : c.tape j (c.head j) = c.tape (B.select c.state) (c.head (B.select c.state)) := by rw [atState, selected]
        rw [symbol, advance_read B data c state .left input auxiliary index] at one
        simpa [d, atState, selected, atHead, Move.onInt] using one
      have rest := ih d atState (by simp [d]) input auxiliary index
      have path := step.trans B rest
      simpa [d, Function.update_idem, Nat.add_comm] using path

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
