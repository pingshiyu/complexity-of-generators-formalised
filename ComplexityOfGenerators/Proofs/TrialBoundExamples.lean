import ComplexityOfGenerators.Foundations.TrialBounds
import ComplexityOfGenerators.Proofs.EmptyTrialOverhead

/-! The separate-budget specification admits the delayed empty generator with
exactly its real cost: one setup step plus one step per supplied random bit. -/

namespace ComplexityOfGenerators

variable (α : Type) [Fintype α]

theorem delayedEmptyGenerator_language (data : InputData Unit Bool) :
    (delayedEmptyGenerator α).generatedLanguage data = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro word ⟨bits, nonempty, t, produced⟩
  cases t with
  | zero =>
      simp [Machine.run, Machine.observe, Machine.initialConfiguration, delayedEmptyGenerator] at produced
  | succ t =>
      rw [delayedEmptyGenerator_run] at produced
      split_ifs at produced; cases produced

/-- The additional step is accounted for without supplying an additional bit. -/
theorem delayedEmptyGenerator_trialBound (data : InputData Unit Bool) (seed : ℕ) :
    (delayedEmptyGenerator α).TrialBound data seed (seed + 1) := by
  refine ⟨?_, ?_⟩
  · intro bits length
    exact ⟨.exhausted, by rw [delayedEmptyGenerator_run]; simp [show ¬ seed < bits.length by omega]⟩
  · intro bits length
    rw [delayedEmptyGenerator_language]
    simp only [Set.not_nonempty_empty, iff_false]
    rintro ⟨word, t, produced⟩
    have exhausted : (delayedEmptyGenerator α).run data bits (seed + 1) = .halted .exhausted := by
      rw [delayedEmptyGenerator_run]
      simp [length]
    have impossible := (delayedEmptyGenerator α).halted_outcome_unique data bits t (seed + 1)
      (.accepted word) .exhausted produced exhausted
    cases impossible

/-- Both budgets can be uniform polynomials in the family index. -/
theorem delayedEmptyGenerator_polynomial_trials :
    ∃ seed time : PolynomialBound, ∀ n,
      (delayedEmptyGenerator α).TrialBound (generatorData n) (seed n) (time n) := by
  let seed : PolynomialBound := ⟨1, 1, by decide⟩
  let time : PolynomialBound := ⟨2, 1, by decide⟩
  refine ⟨seed, time, fun n => ?_⟩
  exact Machine.TrialBound.mono_time _ (delayedEmptyGenerator_trialBound α (generatorData n) (seed n))
    (by simp [seed, time, PolynomialBound.eval])

/-- The delayed implementation now witnesses polynomial generation of the empty
language in the actual `PG` definition, not just in an auxiliary specification. -/
theorem delayed_empty_language_in_pg : (∅ : Language α) ∈ PG α := by
  let G : GeneratorFamily α := {
    machine := delayedEmptyGenerator α
    isGenerator := fun n => delayedEmptyGenerator_isGenerator α (generatorData n)
    outputLength := by
      intro n word member
      change word ∈ (delayedEmptyGenerator α).generatedLanguage (generatorData n) at member
      rw [delayedEmptyGenerator_language] at member
      exact False.elim member }
  refine ⟨G, ?_, delayedEmptyGenerator_polynomial_trials α⟩
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro word ⟨n, member⟩
  change word ∈ (delayedEmptyGenerator α).generatedLanguage (generatorData n) at member
  rw [delayedEmptyGenerator_language] at member
  exact member

end ComplexityOfGenerators
