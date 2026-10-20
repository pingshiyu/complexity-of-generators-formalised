import ComplexityOfGenerators.Simulation.WordStack.Commands

/-! A bounded-loop rule for actual stack-command executions. The invariant
and a decreasing natural-valued measure account for every possible body result,
including random-tape exhaustion. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ}

theorem loop_bounded (j : Fin k) (test : Observation S → Bool) (body : Command S O k)
    (n : ℕ) (bits : BitString) (invariant : Memory S O k → Prop) (measure : Memory S O k → ℕ)
    (budget : ℕ)
    (positive : ∀ m, invariant m → test (observe n m j) = true → 0 < measure m)
    (step : ∀ m, invariant m → test (observe n m j) = true →
      ∃ t ≤ budget, ∃ result, body.Runs n bits m t result ∧
        match result with
        | .done finish => invariant finish ∧ measure finish < measure m
        | .exhausted => True)
    (m : Memory S O k) (initial : invariant m) :
    ∃ t ≤ measure m * (budget + 2), ∃ result, (loop j test body).Runs n bits m t result ∧
      match result with
      | .done finish => invariant finish ∧ test (observe n finish j) = false
      | .exhausted => True := by
  generalize equation : measure m = count
  induction count using Nat.strong_induction_on generalizing m with
  | h count ih =>
    cases guard : test (observe n m j) with
    | false => exact ⟨0, by omega, .done m, Runs.loop_stop m j test body guard, initial, guard⟩
    | true =>
      have nonzero := positive m initial guard
      obtain ⟨s, cost, result, run, preserved⟩ := step m initial guard
      cases result with
      | exhausted =>
        refine ⟨1 + s, ?_, .exhausted, Runs.loop_absent m j test body s guard run, trivial⟩
        have mul := Nat.mul_le_mul_right (budget + 2) (show 1 ≤ count by omega)
        nlinarith
      | done middle =>
        obtain ⟨inv, decreases⟩ := preserved
        obtain ⟨t, cost', result, rest, finished⟩ := ih (measure middle) (by omega) middle inv rfl
        refine ⟨1 + s + 1 + t, ?_, result,
          Runs.loop m middle j test body s t result guard run rest, finished⟩
        have mul := Nat.mul_le_mul_right (budget + 2) (show measure middle + 1 ≤ count by omega)
        nlinarith

end ComplexityOfGenerators.Simulation.WordStack.Command
