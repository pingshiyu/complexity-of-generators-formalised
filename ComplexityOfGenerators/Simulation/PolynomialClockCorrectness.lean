import ComplexityOfGenerators.Simulation.ClockBootstrap
import ComplexityOfGenerators.Foundations.BoundedGeneration

/-!
# End-to-end native polynomial clocking

The compiler starts on a blank tape, constructs its odometer, restores the
physical input head, and simulates the source. It always halts in polynomial
time and preserves exactly the outputs accepted by the source within its
deadline. No source termination or bound on the supplied random tape is needed.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

def polynomialClockTimePolynomial (p : PolynomialBound) : Polynomial ℕ :=
  let size : Polynomial ℕ := Polynomial.X + 1
  let time := p.asPolynomial.comp size
  6 * Polynomial.X + 15 + (time + 1) *
    (2 * time + Polynomial.C (p.degree + 1) * (2 * size + 5) + 5)

def polynomialClockTime (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (polynomialClockTimePolynomial p)

theorem polynomialClockTime_bound (p : PolynomialBound) (n : ℕ) :
    6 * n + 15 + (p (n + 1) + 1) *
      (2 * p (n + 1) + (p.degree + 1) * (2 * (n + 1) + 5) + 5) ≤ polynomialClockTime p n := by
  simpa [polynomialClockTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    PolynomialBound.asPolynomial_eval, polynomialClockTime] using
    PolynomialBound.eval_le_ofPolynomial (polynomialClockTimePolynomial p) n

variable {I O : Type} [Fintype I] [Fintype O] (M : Machine I Bool O) (p : PolynomialBound)

theorem polynomialClockMachine_run (w : List I) (bits : BitString) :
    ∃ result,
      (polynomialClockMachine M p).run (decisionData w) bits (polynomialClockTime p w.length) = .halted result ∧
      result.acceptedWord = (M.run (decisionData w) bits (p (w.length + 1))).acceptedWord := by
  let L := clockPreparedLoader M p
  let routine := polynomialClockRoutine M p
  let C := polynomialClockMachine M p
  let data := decisionData w
  let cost := (p (w.length + 1) + 1) * (2 * p (w.length + 1) + (p.degree + 1) * (2 * (w.length + 1) + 5) + 5)
  obtain ⟨ready, related, loaded⟩ := polynomialClockMachine_loaded M p w bits
  obtain ⟨result, execution, output⟩ := clock_simulates_bounded_run M p data bits (w.length + 1) ready related
  have lifted := sequence_right_runFrom L routine data bits ready cost
  change C.runFrom data bits (sequenceRightConfiguration L routine ready) cost =
    sequenceRightResult L routine ((polynomialClockCore M p).runFrom data bits ready cost) at lifted
  rw [execution] at lifted
  have halted : C.run data bits (6 * w.length + 15 + cost) = .halted result := by
    rw [← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ (6 * w.length + 15)
      (by simpa using loaded)]
    exact lifted
  have time : 6 * w.length + 15 + cost ≤ polynomialClockTime p w.length := polynomialClockTime_bound p w.length
  have padded := C.run_halted_add data bits _ result halted (polynomialClockTime p w.length - (6 * w.length + 15 + cost))
  exact ⟨result, by simpa only [Nat.add_sub_of_le time] using padded, output⟩

/-- Every branch is bounded, including empty and overlong finite choice tapes. -/
theorem polynomialClockMachine_timeBound (w : List I) :
    (polynomialClockMachine M p).TimeBound (decisionData w) (polynomialClockTime p w.length) := by
  intro bits
  obtain ⟨result, halted, _⟩ := polynomialClockMachine_run M p w bits
  exact ⟨result, halted⟩

theorem polynomialClockMachine_produces_iff (w : List I) (bits : BitString) (out : List O) :
    (polynomialClockMachine M p).Produces (decisionData w) bits out ↔
      M.run (decisionData w) bits (p (w.length + 1)) = .halted (.accepted out) := by
  obtain ⟨result, halted, output⟩ := polynomialClockMachine_run M p w bits
  have sourceOutput : (M.run (decisionData w) bits (p (w.length + 1))).acceptedWord = some out ↔
      M.run (decisionData w) bits (p (w.length + 1)) = .halted (.accepted out) := by
    cases M.run (decisionData w) bits (p (w.length + 1)) with
    | running c => simp [RunState.acceptedWord]
    | halted result => cases result <;> simp [RunState.acceptedWord, Outcome.acceptedWord]
  constructor
  · intro produced
    obtain ⟨s, hs⟩ := produced
    have same := (polynomialClockMachine M p).halted_outcome_unique (decisionData w) bits _ s result (.accepted out) halted hs
    rw [same] at output
    exact sourceOutput.mp output.symm
  · intro accepted
    have equal : result.acceptedWord = some out := output.trans (sourceOutput.mpr accepted)
    have same : result = .accepted out := by
      cases result with
      | accepted word => simpa [Outcome.acceptedWord] using equal
      | rejected => simp [Outcome.acceptedWord] at equal
      | exhausted => simp [Outcome.acceptedWord] at equal
    exact ⟨_, by simpa only [same] using halted⟩

end

end ComplexityOfGenerators.Simulation
