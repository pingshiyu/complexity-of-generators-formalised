import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

/-!
# Separate seed and execution budgets

This repair of the Remark 1 convention keeps exhaustion as the only
permitted rejection and keeps the full-trial emptiness test. It separates the
number of supplied random bits from the number of primitive transitions, so
that ordinary simulation overhead can be charged without lengthening the tape.
`PG` uses a uniform polynomial for each budget, as specified in
`UniformGenerators.PolynomialTime`.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

/-- Increasing the execution allowance leaves the random experiment unchanged. -/
theorem TrialBound.mono_time {data : InputData I A} {seed s t : ℕ}
    (bound : M.TrialBound data seed s) (time : s ≤ t) : M.TrialBound data seed t :=
  ⟨fun bits length => M.haltsWithin_mono data bits time (bound.1 bits length), bound.2⟩

/-- The finite seed certificate remains complete for every generated word,
including words originally witnessed by arbitrarily long random tapes. -/
theorem trialBound_budget_witness (data : InputData I A) (seed time : ℕ)
    (positive : 0 < seed) (bound : M.TrialBound data seed time) (word : List O) :
    word ∈ M.generatedLanguage data ↔ ∃ bits : BitString,
      bits.length = seed ∧ M.run data bits time = .halted (.accepted word) :=
  M.generatedLanguage_iff_budget_seed data seed time positive bound word

/-- The separation preserves exactly the emptiness observation from
Remark 1: a full trial exhausts iff the generated slice is empty. -/
theorem trialBound_exhausted_iff_empty (data : InputData I A) (seed time : ℕ)
    (generator : M.IsGenerator data) (bound : M.TrialBound data seed time)
    (bits : BitString) (length : bits.length = seed) :
    M.run data bits time = .halted .exhausted ↔ M.generatedLanguage data = ∅ :=
  bounded_trial_exhausted_iff_empty M data seed time bits generator bound length

/-- Nonempty slices still give ordinary runtime bounds for an attacker with
an arbitrary finite random tape. -/
theorem TrialBound.timeBound_of_nonempty {data : InputData I A} {seed time : ℕ}
    (bound : M.TrialBound data seed time)
    (nonempty : (M.generatedLanguage data).Nonempty) : M.TimeBound data time :=
  M.generatorTimeBound_timeBound_of_nonempty data seed time bound nonempty

end ComplexityOfGenerators.Machine
