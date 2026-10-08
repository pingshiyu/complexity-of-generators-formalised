import ComplexityOfGenerators.Simulation.TapeBankExecution

namespace ComplexityOfGenerators.Simulation.TapeBank

variable {Q S : Type} {k : ℕ} (B : TapeBank Q S k)

/-- A left scan of a virtual tape, including the final control transfer at
the origin. No contents or physical input heads change. -/
theorem rewind (word : BitString) (q next : Q) (j : Fin k)
    (select : B.select q = j)
    (table : ∀ input origin symbol, B.transition q input origin symbol =
      .step (if origin then next else q) symbol (if origin then .stay else .left) .stay)
    (distance : ℕ) (c : BankConfiguration Q S k)
    (state : c.state = q) (head : c.head j = (distance : ℤ))
    (bound : c.inputHead ≤ word.length) :
    B.Steps word c (distance + 1) {c with state := next, head := Function.update c.head j 0} := by
  induction distance generalizing c with
  | zero =>
      have action : B.instruction word c = .step next (c.tape j (c.head j)) .stay .stay := by
        simp [instruction, state, select, head, table]
      have run := Steps.single B word c next _ .stay .stay action
      have adv := advance_stay B word c next bound
      simp only [state, select] at adv
      rw [adv] at run
      have head' : Function.update c.head j 0 = c.head := by
        change c.head j = 0 at head
        rw [← head]
        exact Function.update_eq_self j c.head
      simpa [head'] using run
  | succ distance ih =>
      have nonzero : c.head j ≠ 0 := by omega
      have action : B.instruction word c = .step q (c.tape j (c.head j)) .left .stay := by
        simp [instruction, state, select, table, nonzero]
      let d := {c with state := q, head := Function.update c.head j (c.head j - 1)}
      have step : B.Steps word c 1 d := by
        have run := Steps.single B word c q _ .left .stay action
        have adv := advance_read B word c q .left bound
        simp only [state, select] at adv
        rw [adv] at run
        exact run
      have dhead : d.head j = (distance : ℤ) := by simp [d, head]
      have rest := ih d rfl dhead bound
      have combined := step.trans B rest
      simpa [d, Function.update_idem, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using combined

end ComplexityOfGenerators.Simulation.TapeBank
