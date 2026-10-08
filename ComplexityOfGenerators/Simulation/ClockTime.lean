import ComplexityOfGenerators.Simulation.ClockProgress

/-!
# Bounded execution of the native polynomial clock

Starting from a correctly prepared tape, the native clock always terminates,
even when the source diverges or receives an arbitrarily long choice tape. Its
accepted output is exactly the output accepted by the source by the supplied
deadline. The cost includes the work-head round trips and every digit scan.

The loading of the initial tape is a separate obligation; these results do not
assume that prepared tapes are available in the definition of `P` or `NP`.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite I] [Finite A] [Fintype O]
variable (M : Machine I A O) (p : PolynomialBound)

theorem clock_simulates_bounded_runFrom (data : InputData I A) (bits : BitString) (length fuel r : ℕ)
    (digits : List ℕ) (size : digits.length = p.degree) (bounded : ∀ d ∈ digits, d ≤ length)
    (remaining : Fin (p.coefficient + 1)) (budget : fuel = clockFuel length remaining.val digits)
    (source : Configuration M) (negative : Bool) (target : Configuration (polynomialClockCore M p))
    (related : ClockReady M p length digits remaining source negative target)
    (resources : M.ConfigurationBound data r source) :
    ∃ ticks result,
      ticks ≤ (fuel + 1) * (2 * (r + fuel) + (p.degree + 1) * (2 * length + 5) + 5) ∧
      (polynomialClockCore M p).runFrom data bits target ticks = .halted result ∧
      result.acceptedWord = (M.runFrom data bits source fuel).acceptedWord := by
  induction fuel generalizing r digits remaining source negative target with
  | zero =>
      have zero : remaining.val = 0 := by
        by_contra nonzero
        have pos := clockFuel_positive length remaining.val digits (by omega) bounded
        omega
      obtain ⟨result, halted, output⟩ := clock_expired M p data bits length digits remaining zero source negative target related
      exact ⟨0, result, by omega, halted, output⟩
  | succ fuel ih =>
      have positive : 0 < remaining.val := by
        by_contra h
        have zero : remaining.val = 0 := by omega
        simp [clockFuel, zero] at budget
      have bounds : ReadHeadBounds M data source :=
        ⟨resources.inputHead, resources.auxiliaryHead, resources.indexHead⟩
      cases observed : M.observe data bits source with
      | halted result =>
          obtain ⟨ticks, time, halted⟩ := clock_simulates_halted M p data bits length digits size bounded remaining
            positive source negative target related bounds result observed
          refine ⟨ticks, result, ?_, halted, ?_⟩
          · have head := resources.workHead_natAbs M
            nlinarith
          · rw [M.runFrom_halted data bits source result observed (fuel + 1)]
            rfl
      | running current =>
          have same := M.observe_running_eq data bits source current observed
          subst current
          obtain ⟨nextSource, next⟩ := M.next_running_of_observe_running data bits source observed
          have nextResources : M.ConfigurationBound data (r + 1) nextSource := by
            simpa only [next, Machine.ExecutionBound] using M.next_executionBound data bits r source resources
          obtain ⟨ticks, ready, nextNegative, time, readyRelated, readyRun⟩ := clock_simulates_next M p data bits length
            digits size bounded remaining positive source nextSource negative target related bounds next
          have nextBudget : fuel = clockFuel length
              (clockNextBlock p remaining (clockDigitIncrement length digits).2).val (clockDigitIncrement length digits).1 := by
            have decrease := clockFuel_increment length remaining.val digits positive bounded
            change fuel = clockFuel length
              (if (clockDigitIncrement length digits).2 then remaining.val - 1 else remaining.val)
              (clockDigitIncrement length digits).1
            omega
          obtain ⟨tailTime, result, tailBound, tailRun, output⟩ := ih (r + 1)
            (clockDigitIncrement length digits).1 ((clockDigitIncrement_length length digits).trans size)
            (clockDigitIncrement_bounded length digits bounded)
            (clockNextBlock p remaining (clockDigitIncrement length digits).2) nextBudget
            nextSource nextNegative ready readyRelated nextResources
          refine ⟨ticks + tailTime, result, ?_, ?_, ?_⟩
          · have head := resources.workHead_natAbs M
            nlinarith
          · rw [(polynomialClockCore M p).runFrom_add data bits target ready ticks readyRun]
            exact tailRun
          · rw [M.runFrom_shift data bits source nextSource observed next fuel]
            exact output

/-- A fixed quadratic-in-fuel deadline for the prepared core. Acceptance at
the source deadline is preserved, and any still-running computation is stopped. -/
theorem clock_simulates_bounded_run (data : InputData I A) (bits : BitString)
    (length : ℕ) (target : Configuration (polynomialClockCore M p))
    (related : ClockReady M p length (List.replicate p.degree 0) ⟨p.coefficient, by omega⟩
      M.initialConfiguration false target) :
    ∃ result,
      (polynomialClockCore M p).runFrom data bits target
        ((p length + 1) * (2 * p length + (p.degree + 1) * (2 * length + 5) + 5)) = .halted result ∧
      result.acceptedWord = (M.run data bits (p length)).acceptedWord := by
  obtain ⟨ticks, result, time, halted, output⟩ := clock_simulates_bounded_runFrom M p data bits length (p length) 0
    (List.replicate p.degree 0) (by simp) (by simp) ⟨p.coefficient, by omega⟩ (clockFuel_initial p length).symm
    M.initialConfiguration false target related (M.initialConfiguration_bound data)
  simp only [Nat.zero_add] at time
  have padded := (polynomialClockCore M p).runFrom_halted_add data bits target ticks result halted
    ((p length + 1) * (2 * p length + (p.degree + 1) * (2 * length + 5) + 5) - ticks)
  exact ⟨result, by simpa only [Nat.add_sub_of_le time] using padded, by simpa using output⟩

end

end ComplexityOfGenerators.Simulation
