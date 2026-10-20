import ComplexityOfGenerators.Simulation.WordStack.Compiler
import ComplexityOfGenerators.Proofs.GeneratorCriteria
import ComplexityOfGenerators.Foundations.TrialBounds

/-! Generator criteria for finite word-stack programs, using the proved native
compiler. All time bounds below count actual primitive stack instructions. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Program

variable {Q S O : Type} {k : ℕ} [Fintype Q] [Fintype S] [Fintype O]
    (P : Program Q S O k)

theorem generatedLanguage (n : ℕ)
    (terminates : ∀ bits, ∃ t result, P.Executes n bits P.initialConfiguration t result) :
    P.machine.generatedLanguage (generatorData n) =
      {x | ∃ bits, bits ≠ [] ∧ ∃ t, P.Executes n bits P.initialConfiguration t (.accepted x)} := by
  ext x
  constructor
  · rintro ⟨bits, nonempty, time, output⟩
    obtain ⟨t, result, exec⟩ := terminates bits
    obtain ⟨ticks, _, run⟩ := P.run_compiled exec
    have equal := P.machine.halted_outcome_unique (generatorData n) bits ticks time _ _ run output
    exact ⟨bits, nonempty, t, equal ▸ exec⟩
  · rintro ⟨bits, nonempty, t, exec⟩
    obtain ⟨ticks, _, run⟩ := P.run_compiled exec
    exact ⟨bits, nonempty, ticks, run⟩

theorem haltingTransducer (n : ℕ)
    (terminates : ∀ bits, ∃ t result, P.Executes n bits P.initialConfiguration t result ∧ result ≠ .rejected) :
    P.machine.HaltingTransducer (generatorData n) := by
  constructor
  · intro bits
    obtain ⟨t, result, exec, _⟩ := terminates bits
    obtain ⟨ticks, _, run⟩ := P.run_compiled exec
    exact ⟨ticks, result, run⟩
  · intro bits time rejected
    obtain ⟨t, result, exec, notRejected⟩ := terminates bits
    obtain ⟨ticks, _, run⟩ := P.run_compiled exec
    exact notRejected (P.machine.halted_outcome_unique (generatorData n) bits ticks time _ _ run rejected)

noncomputable def compiledTime (time : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (1 + (2 * time.asPolynomial + 1) * (4 * time.asPolynomial + 4))

theorem compiledTime_bound (time : PolynomialBound) (n t : ℕ) (bound : t ≤ time n) :
    1 + (2 * t + 1) * (4 * t + 4) ≤ compiledTime time n := by
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one,
    Polynomial.eval_ofNat, PolynomialBound.asPolynomial_eval]
  gcongr

/-- This criterion transfers an implemented stack generator to `PG`. Its
hypotheses concern executions of one fixed finite program, not an abstract
oracle for a word-valued function. -/
theorem mem_pg (L : Language O) (seed time : PolynomialBound)
    (terminates : ∀ n bits, ∃ t result,
      P.Executes n bits P.initialConfiguration t result ∧ result ≠ .rejected)
    (sound : ∀ n bits t x, P.Executes n bits P.initialConfiguration t (.accepted x) → x ∈ lengthSlice L n)
    (complete : ∀ n x, x ∈ lengthSlice L n → ∃ bits, bits.length = seed n ∧
      ∃ t, P.Executes n bits P.initialConfiguration t (.accepted x))
    (productive : ∀ n bits, bits.length = seed n → (lengthSlice L n).Nonempty →
      ∃ t x, P.Executes n bits P.initialConfiguration t (.accepted x))
    (bounded : ∀ n bits, bits.length ≤ seed n → ∃ t ≤ time n, ∃ result,
      P.Executes n bits P.initialConfiguration t result) : L ∈ PG O := by
  have language (n : ℕ) : P.machine.generatedLanguage (generatorData n) = lengthSlice L n := by
    rw [P.generatedLanguage n (fun bits => by
      obtain ⟨t, result, exec, _⟩ := terminates n bits
      exact ⟨t, result, exec⟩)]
    ext x
    constructor
    · rintro ⟨bits, _, t, exec⟩
      exact sound n bits t x exec
    · intro member
      obtain ⟨bits, length, t, exec⟩ := complete n x member
      exact ⟨bits, by intro empty; have := seed.positive n; simp [empty] at length; omega, t, exec⟩
  have full (n : ℕ) (bits : BitString) (length : bits.length = seed n) :
      P.machine.Accepts (generatorData n) bits ↔
        (P.machine.generatedLanguage (generatorData n)).Nonempty := by
    rw [language n]
    constructor
    · rintro ⟨x, t, output⟩
      obtain ⟨s, result, exec, _⟩ := terminates n bits
      obtain ⟨ticks, _, run⟩ := P.run_compiled exec
      have equal := P.machine.halted_outcome_unique (generatorData n) bits ticks t _ _ run output
      exact ⟨x, sound n bits s x (equal ▸ exec)⟩
    · intro nonempty
      obtain ⟨t, x, exec⟩ := productive n bits length nonempty
      obtain ⟨ticks, _, run⟩ := P.run_compiled exec
      exact ⟨x, ticks, run⟩
  refine mem_pg_of_lengthSlices L P.machine seed (compiledTime time) ?_ language ?_
  · intro n
    exact P.machine.isGenerator_of_full_trials (generatorData n) (seed n)
      (P.haltingTransducer n (terminates n)) (full n)
  · intro n
    refine ⟨?_, full n⟩
    intro bits length
    obtain ⟨t, bound, result, exec⟩ := bounded n bits length
    obtain ⟨ticks, cost, run⟩ := P.run_compiled exec
    exact P.machine.haltsWithin_mono (generatorData n) bits
      (cost.trans (compiledTime_bound time n t bound)) ⟨result, run⟩

end ComplexityOfGenerators.Simulation.WordStack.Program
