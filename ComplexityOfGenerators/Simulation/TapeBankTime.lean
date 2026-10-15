import ComplexityOfGenerators.Simulation.TapeBankCompiler
import ComplexityOfGenerators.Simulation.TransducerBank.Time
import ComplexityOfGenerators.Foundations.ResourceBounds

/-! Polynomial simulation of a finite tape bank in the retained native model. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Q S : Type} {k : ℕ} [Fintype Q] [Fintype S] (B : TapeBank Q S k)

/-- The decision-bank translation preserves the general compiler's exact time bound. -/
theorem bank_run (word bits : BitString) (t : ℕ) (result : Bool)
    (exec : B.Executes word B.initialConfiguration t result) :
    ∃ ticks, ticks ≤ 1 + (t + 1) * (2 * t + 4) ∧
      (bankMachine B).run (decisionData word) bits ticks = .halted (bankOutcome result) := by
  exact TransducerBank.bank_run B.toTransducer (decisionData word) bits t (bankOutcome result)
    (by simpa using exec.toTransducer B bits)

/-- A fully operational transfer theorem: a finite tape-bank program with a
polynomial instruction bound gives a native deterministic polynomial decider.
The finite-bank execution proof, rather than computability alone, is required. -/
theorem mem_p_of_tapeBank (L : Language Bool) (p : PolynomialBound)
    (terminates : ∀ word, ∃ t result, t ≤ p word.length ∧
      B.Executes word B.initialConfiguration t result ∧ (result = true ↔ word ∈ L)) :
    L ∈ P Bool := by
  let poly := 1 + (p.asPolynomial + 1) * (2 * p.asPolynomial + 4)
  let time := PolynomialBound.ofPolynomial poly
  have bounded (word : BitString) (bits : BitString) :
      ∃ result, (bankMachine B).run (decisionData word) bits (time word.length) =
        .halted (bankOutcome result) ∧ (result = true ↔ word ∈ L) := by
    obtain ⟨t, result, cost, exec, correct⟩ := terminates word
    obtain ⟨ticks, runtime, run⟩ := bank_run B word bits t result exec
    have bound : ticks ≤ time word.length := by
      calc
        ticks ≤ 1 + (t + 1) * (2 * t + 4) := runtime
        _ ≤ 1 + (p word.length + 1) * (2 * p word.length + 4) := by gcongr
        _ = poly.eval word.length := by simp [poly, PolynomialBound.asPolynomial_eval]
        _ ≤ time word.length := PolynomialBound.eval_le_ofPolynomial poly word.length
    exact ⟨result, by simpa [Nat.add_sub_of_le bound] using
      (bankMachine B).run_halted_add _ _ ticks _ run (time word.length - ticks), correct⟩
  refine ⟨bankMachine B, time, bankMachine_deterministic B, ?_, ?_⟩
  · intro word bits
    obtain ⟨result, run, _⟩ := bounded word bits
    exact ⟨bankOutcome result, run⟩
  · intro word
    obtain ⟨result, run, correct⟩ := bounded word []
    constructor
    · rintro ⟨out, t, accepted⟩
      have same := (bankMachine B).halted_outcome_unique _ _ _ _ _ _ accepted run
      cases result <;> simp_all [bankOutcome]
    · intro member
      have yes := correct.mpr member
      exact ⟨[], time word.length, by simpa [yes, bankOutcome] using run⟩

end
end ComplexityOfGenerators.Simulation
