import ComplexityOfGenerators.Simulation.TransducerBank.Execution

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

/-- A finite self-loop drains randomness using at most the remaining length;
it has no explicit rejection and changes no tape or output. -/
theorem drain_executes (data : InputData I A) (bits : BitString) (state : Q)
    (table : ∀ input auxiliary index origin cell, B.transition state input auxiliary index origin cell = .readRandom state state)
    (fuel : ℕ) (c : BankConfiguration O Q S k) (atState : c.state = state)
    (bound : bits.length ≤ c.randomHead + fuel) :
    ∃ ticks, ticks ≤ fuel ∧ B.Executes data bits c ticks .exhausted := by
  induction fuel generalizing c with
  | zero =>
      refine ⟨0, le_rfl, .exhausted c state state ?_ ?_⟩
      · simp [instruction, atState, table]
      · exact List.getElem?_eq_none (by omega)
  | succ fuel ih =>
      cases lookup : bits[c.randomHead]? with
      | none => exact ⟨0, Nat.zero_le _, .exhausted c state state (by simp [instruction, atState, table]) lookup⟩
      | some bit =>
          obtain ⟨ticks, cost, rest⟩ := ih (choose c state) rfl (by change bits.length ≤ c.randomHead + 1 + fuel; omega)
          refine ⟨ticks + 1, by omega, .random c state state bit ticks .exhausted ?_ lookup ?_⟩
          · simp [instruction, atState, table]
          · simpa using rest

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
