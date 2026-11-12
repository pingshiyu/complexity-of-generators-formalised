import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Machine

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem trialOutcome_sound (n : ℕ) (bits : BitString) (word : List Symbol)
    (accepts : trialOutcome n bits = .accepted word) : word ∈ selfReduction.bases n := by
  unfold trialOutcome expectedOutcome at accepts
  split_ifs at accepts with enough good productive
  · have same : decodeWords n bits = word := Outcome.accepted.inj accepts
    rw [← same]
    exact (verifies_iff_bases _ n (decodeWords_length _ _)).mp good
  · have same : baseDefault n = word := Outcome.accepted.inj accepts
    rw [← same]
    exact baseDefault_mem n productive

theorem trialOutcome_never_rejects (n : ℕ) (bits : BitString) : trialOutcome n bits ≠ .rejected := by
  unfold trialOutcome expectedOutcome
  split_ifs <;> simp

theorem machine_language (n : ℕ) : machine.generatedLanguage (generatorData n) = selfReduction.bases n := by
  ext word
  constructor
  · rintro ⟨bits, _, ticks, accepts⟩
    obtain ⟨referenceTicks, reference⟩ := machine_execution n bits
    have same := machine.halted_outcome_unique (generatorData n) bits referenceTicks ticks _ _ reference accepts
    exact trialOutcome_sound n bits word same
  · intro member
    have size : word.length = n := by
      have ancestor := member.1
      rw [ancestors_eq_slice] at ancestor
      exact ancestor.2
    let bits := encodeWords word ++ [false]
    have enough : 4*n ≤ bits.length := by simp [bits, size]
    have decoded : decodeWords n bits = word := by
      rw [← size]
      exact decodeWords_encode word [false]
    have good : NativeEvaluation.verifies word [] = true := (verifies_iff_bases word n size).mpr member
    obtain ⟨ticks, native⟩ := machine_execution n bits
    refine ⟨bits, by simp [bits], ticks, ?_⟩
    simpa only [trialOutcome, enough, ite_true, expectedOutcome, decoded, good] using native

theorem machine_halting (n : ℕ) : machine.HaltingTransducer (generatorData n) := by
  constructor
  · intro bits
    obtain ⟨ticks, run⟩ := machine_execution n bits
    exact ⟨ticks, _, run⟩
  · intro bits ticks rejects
    obtain ⟨referenceTicks, reference⟩ := machine_execution n bits
    have same := machine.halted_outcome_unique (generatorData n) bits referenceTicks ticks _ _ reference rejects
    exact trialOutcome_never_rejects n bits same

theorem machine_accepts_full (n : ℕ) (bits : BitString) (enough : 4*n ≤ bits.length) :
    machine.Accepts (generatorData n) bits ↔ BaseProductive n := by
  constructor
  · rintro ⟨word, ticks, accepts⟩
    obtain ⟨referenceTicks, reference⟩ := machine_execution n bits
    have same := machine.halted_outcome_unique (generatorData n) bits referenceTicks ticks _ _ reference accepts
    exact (bases_productive_iff n).mp ⟨word, trialOutcome_sound n bits word same⟩
  · intro productive
    obtain ⟨ticks, run⟩ := machine_execution n bits
    cases good : NativeEvaluation.verifies (decodeWords n bits) [] with
    | false => exact ⟨baseDefault n, ticks, by simpa [trialOutcome, enough, expectedOutcome, good, productive] using run⟩
    | true => exact ⟨decodeWords n bits, ticks, by simpa [trialOutcome, enough, expectedOutcome, good] using run⟩

theorem full_trial (n : ℕ) (bits : BitString) (length : bits.length = seed n) :
    machine.Accepts (generatorData n) bits ↔ (machine.generatedLanguage (generatorData n)).Nonempty := by
  have enough : 4*n ≤ bits.length := by simp only [length, seed, PolynomialBound.eval, pow_one]; omega
  rw [machine_accepts_full n bits enough, machine_language, bases_productive_iff]

theorem machine_generator (n : ℕ) : machine.IsGenerator (generatorData n) :=
  machine.isGenerator_of_full_trials (generatorData n) (seed n) (machine_halting n) (full_trial n)

theorem machine_trialBound (n : ℕ) :
    machine.GeneratorTimeBound (generatorData n) (seed n) (time n) :=
  ⟨machine_bounded n, full_trial n⟩

/-- All constant-formula bases have positive support; a verifier failure uses
an actual native fallback, so no rejection sampling or oracle is assumed. -/
noncomputable def baseFamily : GeneratorFamily Symbol where
  machine := machine
  isGenerator := machine_generator
  outputLength := by
    intro n word member
    change word ∈ machine.generatedLanguage (generatorData n) at member
    rw [machine_language] at member
    have ancestor := member.1
    rw [ancestors_eq_slice] at ancestor
    exact ancestor.2

theorem baseFamily_language (n : ℕ) :
    baseFamily.toUniformGenerators.layer n = selfReduction.bases n := machine_language n

theorem baseFamily_polynomialTime : baseFamily.toUniformGenerators.PolynomialTime :=
  ⟨seed, time, machine_trialBound⟩

end
end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
