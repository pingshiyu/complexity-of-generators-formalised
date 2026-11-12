import ComplexityOfGenerators.Simulation.RandomMeter.Execution
import ComplexityOfGenerators.Proofs.GeneratorCriteria

/-!
# Accepting-time to trial-budget normalization for arbitrary input data

The compiler preserves both read-only words and the unary index. It consumes
one random fuel bit per source instruction, and never hides a computation in
finite control. Thus every finite tape bounds the compiled runtime even for
empty source languages, where the accepting-time requirement is vacuous.
-/
namespace ComplexityOfGenerators.Simulation.RandomMeter
noncomputable section
variable {I A O : Type} (M : Machine I A O)

theorem produces_iff_value (data : InputData I A) (bits : BitString) (word : Word O) :
    (machine M).Produces data bits word ↔ value M data M.initialConfiguration bits=.accepted word := by
  constructor
  · rintro ⟨ticks,accepted⟩
    have same := (machine M).halted_outcome_unique data bits (3*bits.length) ticks _ _ (run M data bits) accepted
    cases output : value M data M.initialConfiguration bits with
    | accepted result => simpa [output,rejectDrainOutcome] using same
    | rejected => simp [output,rejectDrainOutcome] at same
    | exhausted => simp [output,rejectDrainOutcome] at same
  · intro accepted
    refine ⟨3*bits.length,?_⟩
    simpa only [accepted,rejectDrainOutcome] using run M data bits

theorem generatedLanguage (data : InputData I A) :
    (machine M).generatedLanguage data=M.generatedLanguage data := by
  ext word
  rw [(machine M).mem_generatedLanguage_iff_produces data word,M.mem_generatedLanguage_iff_produces data word]
  constructor
  · rintro ⟨bits,produced⟩
    exact (value_accepting M data M.initialConfiguration bits word
      ((produces_iff_value M data bits word).mp produced)).produces M
  · rintro ⟨bits,produced⟩
    obtain ⟨log,trace⟩ := (M.produces_iff_acceptingTranscript data word).mp ⟨bits,produced⟩
    exact ⟨log,(produces_iff_value M data log word).mpr (value_of_accepting M trace)⟩

theorem haltingTransducer (data : InputData I A) : (machine M).HaltingTransducer data := by
  constructor
  · intro bits
    exact ⟨3*bits.length,rejectDrainOutcome (value M data M.initialConfiguration bits),run M data bits⟩
  · intro bits ticks rejected
    have same := (machine M).halted_outcome_unique data bits (3*bits.length) ticks _ _ (run M data bits) rejected
    cases output : value M data M.initialConfiguration bits <;> simp [output,rejectDrainOutcome] at same

theorem full_trial (data : InputData I A) (deadline seed : ℕ) (long : deadline<seed)
    (noReject : ∀ bits : BitString,∀ ticks,M.run data bits ticks≠.halted .rejected)
    (activeTime : (M.generatedLanguage data).Nonempty → M.TimeBound data deadline)
    (bits : BitString) (length : bits.length=seed) :
    (machine M).Accepts data bits ↔ ((machine M).generatedLanguage data).Nonempty := by
  constructor
  · exact fun accepted=>((machine M).generatedLanguage_nonempty_iff_accepts data).mpr ⟨bits,accepted⟩
  · intro active
    rw [generatedLanguage M data] at active
    have total : ∀ seed : BitString,∃ result,M.runFrom data seed M.initialConfiguration deadline=.halted result := by
      intro seed
      simpa only [Machine.runFrom_initial,Machine.HaltsWithin] using activeTime active seed
    have nonreject : ∀ seed : BitString,∀ ticks,
        M.runFrom data seed M.initialConfiguration ticks≠.halted .rejected := by
      simpa only [Machine.runFrom_initial] using noReject
    obtain ⟨word,accepted⟩ := value_accepts_of_total M data deadline M.initialConfiguration rfl total nonreject bits (by omega)
    exact ⟨word,(produces_iff_value M data bits word).mpr accepted⟩

theorem isGenerator (data : InputData I A) (deadline seed : ℕ) (long : deadline<seed)
    (noReject : ∀ bits : BitString,∀ ticks,M.run data bits ticks≠.halted .rejected)
    (activeTime : (M.generatedLanguage data).Nonempty → M.TimeBound data deadline) :
    (machine M).IsGenerator data := by
  apply Machine.isGenerator_of_full_trials _ data seed
  · exact haltingTransducer M data
  · exact full_trial M data deadline seed long noReject activeTime

theorem trialBound (data : InputData I A) (deadline seed : ℕ) (long : deadline<seed)
    (noReject : ∀ bits : BitString,∀ ticks,M.run data bits ticks≠.halted .rejected)
    (activeTime : (M.generatedLanguage data).Nonempty → M.TimeBound data deadline) :
    (machine M).GeneratorTimeBound data seed (3*seed) := by
  constructor
  · intro bits short
    have native := run M data bits
    have bound : 3*bits.length≤3*seed := by omega
    refine ⟨rejectDrainOutcome (value M data M.initialConfiguration bits),?_⟩
    simpa only [Nat.add_sub_of_le bound] using (machine M).run_halted_add data bits (3*bits.length) _ native (3*seed-3*bits.length)
  · exact full_trial M data deadline seed long noReject activeTime

/-- The generic input-data accepting-time bridge. No bound on short trials of
an empty source member is assumed. -/
theorem trialBound_of_accepting (data : InputData I A) (deadline seed : ℕ) (long : deadline<seed)
    (generator : M.IsGenerator data) (bounded : M.AcceptingTimeBound data deadline) :
    (machine M).GeneratorTimeBound data seed (3*seed) :=
  trialBound M data deadline seed long generator.1.2
    (fun active=>M.accepting_timeBound_of_nonempty data deadline generator bounded active)

theorem isGenerator_of_accepting (data : InputData I A) (deadline seed : ℕ) (long : deadline<seed)
    (generator : M.IsGenerator data) (bounded : M.AcceptingTimeBound data deadline) :
    (machine M).IsGenerator data :=
  isGenerator M data deadline seed long generator.1.2
    (fun active=>M.accepting_timeBound_of_nonempty data deadline generator bounded active)

def seed (p : PolynomialBound) : PolynomialBound := AcceptingTimeGeneration.seed p

def time (p : PolynomialBound) : PolynomialBound :=
  (⟨3,0,by decide⟩ : PolynomialBound).mul (seed p)

theorem seed_long (p : PolynomialBound) (n : ℕ) : p n<seed p n := by
  have lower := AcceptingTimeGeneration.seed_lower p n
  change p n<AcceptingTimeGeneration.seed p n
  omega

theorem time_eval (p : PolynomialBound) (n : ℕ) : time p n=3*seed p n := by
  rw [time,PolynomialBound.mul_eval]
  change 3*seed p n=3*seed p n
  rfl

theorem polynomial_trialBound_of_accepting (p : PolynomialBound) (data : InputData I A)
    (generator : M.IsGenerator data) (bounded : M.AcceptingTimeBound data (p data.index)) :
    (machine M).GeneratorTimeBound data (seed p data.index) (time p data.index) := by
  rw [time_eval]
  exact trialBound_of_accepting M data _ _ (seed_long p data.index) generator bounded

theorem polynomial_trialBound (p : PolynomialBound) (data : InputData I A)
    (noReject : ∀ bits : BitString,∀ ticks,M.run data bits ticks≠.halted .rejected)
    (activeTime : (M.generatedLanguage data).Nonempty → M.TimeBound data (p data.index)) :
    (machine M).GeneratorTimeBound data (seed p data.index) (time p data.index) := by
  rw [time_eval]
  exact trialBound M data _ _ (seed_long p data.index) noReject activeTime

end
end ComplexityOfGenerators.Simulation.RandomMeter
