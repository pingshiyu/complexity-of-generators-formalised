import ComplexityOfGenerators.Simulation.TapeBankStep
import ComplexityOfGenerators.Foundations.ResourceBounds

/-! Polynomial simulation of a finite tape bank in the retained native model. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {Q S : Type} {k : ℕ} [Fintype Q] [Fintype S] (B : TapeBank Q S k)

def bankOutcome (accepted : Bool) : Outcome Unit :=
  if accepted then .accepted [] else .rejected

theorem bank_terminal (word bits : BitString) (r : ℕ) (source : BankConfiguration Q S k)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (h : BankReady B source negative start) (bounded : B.Bounded word r source)
    (result : Bool) (table : B.instruction word source = if result then .accept else .reject) :
    (bankMachine B).runFrom (decisionData word) bits start
      (source.head (B.select source.state)).natAbs = .halted (bankOutcome result) := by
  obtain ⟨ready, scan, run⟩ := bank_seek B word bits r source negative start h bounded
  rw [run]
  have snap := h.toBankSnapshot.scan B scan
  have memory := snap.memory
  unfold BankMemory at memory
  unfold TapeBank.instruction at table
  cases result <;>
    simp [Machine.observe, bankMachine, bankTransition, scan.state, h.state,
      scan.head, memory, bankCell, decisionData, snap.input, table, bankOutcome, snap.output]

/-- A `t`-instruction bank execution from radius `r` takes at most
`(t+1)*(2*(r+t)+4)` actual native transitions, including terminal lookup. -/
theorem bank_simulates (word bits : BitString) (source : BankConfiguration Q S k)
    (t : ℕ) (result : Bool) (exec : B.Executes word source t result)
    (r : ℕ) (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (h : BankReady B source negative start) (bounded : B.Bounded word r source) :
    ∃ ticks, ticks ≤ (t + 1) * (2 * (r + t) + 4) ∧
      (bankMachine B).runFrom (decisionData word) bits start ticks = .halted (bankOutcome result) := by
  induction exec generalizing r negative start with
  | accept source table =>
      refine ⟨(source.head (B.select source.state)).natAbs, ?_, ?_⟩
      · have bound := bounded.2 (B.select source.state)
        omega
      · exact bank_terminal B word bits r source negative start h bounded true table
  | reject source table =>
      refine ⟨(source.head (B.select source.state)).natAbs, ?_, ?_⟩
      · have bound := bounded.2 (B.select source.state)
        omega
      · exact bank_terminal B word bits r source negative start h bounded false table
  | step source next write work input t result table rest ih =>
      obtain ⟨s, ready, sides, cost, related, run⟩ :=
        bank_step B word bits r source negative start h bounded next write work input table
      obtain ⟨u, cost', run'⟩ := ih (r + 1) sides ready related
        (B.advance_bounded word r source next write work input bounded)
      refine ⟨s + u, ?_, ?_⟩
      · calc
          s + u ≤ (2 * r + 4) + (t + 1) * (2 * (r + 1 + t) + 4) := Nat.add_le_add cost cost'
          _ ≤ (t + 1 + 1) * (2 * (r + (t + 1)) + 4) := by nlinarith
      · rw [(bankMachine B).runFrom_add _ _ _ ready _ run]
        exact run'

theorem bank_run (word bits : BitString) (t : ℕ) (result : Bool)
    (exec : B.Executes word B.initialConfiguration t result) :
    ∃ ticks, ticks ≤ 1 + (t + 1) * (2 * t + 4) ∧
      (bankMachine B).run (decisionData word) bits ticks = .halted (bankOutcome result) := by
  obtain ⟨ready, related, loaded⟩ := bank_loaded B word bits
  obtain ⟨u, cost, run⟩ := bank_simulates B word bits B.initialConfiguration t result exec
    0 (fun _ => false) ready related (B.initial_bounded word)
  refine ⟨1 + u, by simpa using Nat.add_le_add_left cost 1, ?_⟩
  rw [← (bankMachine B).runFrom_initial] at loaded ⊢
  rw [(bankMachine B).runFrom_add _ _ _ ready _ loaded]
  exact run

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
