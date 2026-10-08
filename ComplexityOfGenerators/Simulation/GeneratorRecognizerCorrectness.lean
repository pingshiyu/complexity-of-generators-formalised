import ComplexityOfGenerators.Simulation.GeneratorRecognizerBootstrap

/-! End-to-end execution of the native generator recognizer, including the
ordinary-input length calculation, virtual-index simulation, and exact output
comparison. Every primitive initialization and simulation step is counted. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

theorem generatorRecognizer_run (w : List α) (bits : BitString) (t : ℕ) (result : Outcome α)
    (execution : M.run (generatorData w.length) bits t = .halted result) :
    (generatorRecognizer M).run (decisionData w) bits
      (6 * w.length + 13 + (t + 1) * (2 * t + 2 * w.length + 8)) = .halted (matcherOutcome w result) := by
  let L := wordIndexPreparedLoader M
  let routine := generatorMatcherRoutine M
  let C := generatorRecognizer M
  let data := decisionData w
  let cost := (t + 1) * (2 * t + 2 * w.length + 8)
  obtain ⟨coreReady, related, loaded⟩ := generatorRecognizer_loaded M w bits
  have simulated := index_simulates_run M (matcherSourceData data) bits w.length t coreReady related result execution
  have matched := outputMatcher_runFrom (virtualIndexCore M) data bits coreReady cost
  rw [simulated] at matched
  have matched' : (outputMatcher (virtualIndexCore M)).runFrom data bits
      (matcherConfiguration (virtualIndexCore M) w coreReady) cost = .halted (matcherOutcome w result) := matched
  have lifted := sequence_right_runFrom L routine data bits (matcherConfiguration (virtualIndexCore M) w coreReady) cost
  change C.runFrom data bits (sequenceRightConfiguration L routine _) cost =
    sequenceRightResult L routine ((outputMatcher (virtualIndexCore M)).runFrom data bits
      (matcherConfiguration (virtualIndexCore M) w coreReady) cost) at lifted
  change C.run data bits (6 * w.length + 13 + cost) = _
  rw [← C.runFrom_initial, C.runFrom_add data bits C.initialConfiguration _ (6 * w.length + 13)
    (by simpa using loaded)]
  exact lifted.trans (congrArg (sequenceRightResult L routine) matched')

def generatorRecognizerTimePolynomial (p : PolynomialBound) : Polynomial ℕ :=
  let time := p.asPolynomial
  6 * Polynomial.X + 13 + (time + 1) * (2 * time + 2 * Polynomial.X + 8)

def generatorRecognizerTime (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (generatorRecognizerTimePolynomial p)

theorem generatorRecognizerTime_bound (p : PolynomialBound) (n : ℕ) :
    6 * n + 13 + (p n + 1) * (2 * p n + 2 * n + 8) ≤ generatorRecognizerTime p n := by
  simpa [generatorRecognizerTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    PolynomialBound.asPolynomial_eval, generatorRecognizerTime] using
    PolynomialBound.eval_le_ofPolynomial (generatorRecognizerTimePolynomial p) n

theorem generatorRecognizer_accepts_at_bound (p : PolynomialBound) (w : List α) (bits : BitString)
    (execution : M.run (generatorData w.length) bits (p w.length) = .halted (.accepted w)) :
    (generatorRecognizer M).run (decisionData w) bits (generatorRecognizerTime p w.length) = .halted (.accepted []) := by
  have simulated := generatorRecognizer_run M w bits (p w.length) (.accepted w) execution
  simp only [matcherOutcome, ↓reduceIte] at simulated
  have time := generatorRecognizerTime_bound p w.length
  have padded := (generatorRecognizer M).run_halted_add (decisionData w) bits _ (.accepted []) simulated
    (generatorRecognizerTime p w.length - (6 * w.length + 13 + (p w.length + 1) * (2 * p w.length + 2 * w.length + 8)))
  simpa only [Nat.add_sub_of_le time] using padded

end

end ComplexityOfGenerators.Simulation
