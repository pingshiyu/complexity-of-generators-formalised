import ComplexityOfGenerators.Proofs.ResourceGeneration
import ComplexityOfGenerators.Proofs.GeneratorCriteria
import ComplexityOfGenerators.Simulation.FamilyClock
import ComplexityOfGenerators.Simulation.RejectDrain

/-!
# Equivalence with the paper's accepting-time polynomial generators

The older `PG` contract bounds finite trials by separate polynomial seed and
execution budgets.  The current paper bounds accepting executions only.
Clocking the source and draining randomness on timeout gives a genuine native
generator satisfying the older trial contract, with the same language.
Consequently the two definitions give the same class of languages.
-/

namespace ComplexityOfGenerators

namespace Machine

theorem AcceptingTimeBound.mono {I A O : Type} {M : Machine I A O}
    {data : InputData I A} {s t : ℕ} (bounded : M.AcceptingTimeBound data s)
    (later : s ≤ t) : M.AcceptingTimeBound data t := by
  intro bits word produced
  simpa only [Nat.add_sub_of_le later] using
    M.run_halted_add data bits s (.accepted word) (bounded bits word produced) (t - s)

theorem accepts_long_tape_of_acceptingTimeBound {I A O : Type}
    (M : Machine I A O) (data : InputData I A) (time : ℕ)
    (generator : M.IsGenerator data) (bounded : M.AcceptingTimeBound data time)
    (bits : BitString) (long : time < bits.length)
    (nonempty : (M.generatedLanguage data).Nonempty) : M.Accepts data bits := by
  have prefixLength : (bits.take (time + 1)).length = time + 1 := by
    simp [List.length_take]; omega
  obtain ⟨word, produced⟩ :=
    (M.accepts_full_prefix_of_acceptingTimeBound data time generator bounded
      (bits.take (time + 1)) prefixLength).mpr nonempty
  exact ⟨word, M.produces_prefix (List.take_prefix _ _) produced⟩

end Machine

namespace Simulation

noncomputable section

/-- Draining explicit rejection preserves output on every individual seed of
an already time-bounded source, even when the source is nondeterministic. -/
theorem rejectDrain_produces_iff_of_timeBound {I A O : Type}
    (M : Machine I A O) (data : InputData I A) (time : ℕ)
    (bounded : M.TimeBound data time) (bits : BitString) (word : List O) :
    (rejectDrain M).Produces data bits word ↔ M.Produces data bits word := by
  constructor
  · rintro ⟨ticks, accepted⟩
    obtain ⟨result, source⟩ := bounded bits
    have target := rejectDrain_run_halted M data bits time result source
    have same := (rejectDrain M).halted_outcome_unique data bits ticks _ _ _ accepted target
    cases result with
    | accepted value =>
        have valueEq : value = word := by simpa [rejectDrainOutcome] using same.symm
        subst value
        exact ⟨time, source⟩
    | rejected => simp [rejectDrainOutcome] at same
    | exhausted => simp [rejectDrainOutcome] at same
  · intro produced
    have source := M.produces_at_bound data bits time word (bounded bits) produced
    exact ⟨time + bits.length, rejectDrain_run_halted M data bits time (.accepted word) source⟩

end
end Simulation

namespace AcceptingTimeGeneration

open Simulation
noncomputable section

variable {α : Type} [Fintype α]

def seed (p : PolynomialBound) : PolynomialBound := p.add ⟨1, 0, by decide⟩

def time (p : PolynomialBound) : PolynomialBound := (polynomialClockTime p).add (seed p)

theorem seed_lower (p : PolynomialBound) (n : ℕ) : p n + 1 ≤ seed p n := by
  simpa only [seed, PolynomialBound.eval, pow_zero, Nat.mul_one] using
    p.add_le (⟨1, 0, by decide⟩ : PolynomialBound) n

def machine (G : UniformGenerators α) (p : PolynomialBound) : Machine Unit Bool α :=
  rejectDrain (familyClock G.machine p)

theorem clock_produces_iff (G : UniformGenerators α) (p : PolynomialBound)
    (bounded : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (p n))
    (n : ℕ) (bits : BitString) (word : Word α) :
    (familyClock G.machine p).Produces (generatorData n) bits word ↔
      G.machine.Produces (generatorData n) bits word := by
  rw [familyClock_produces_iff]
  constructor
  · exact fun accepted => ⟨_, accepted⟩
  · intro produced
    exact ((bounded n).mono (p.monotone (Nat.le_succ n))) bits word produced

theorem produces_iff (G : UniformGenerators α) (p : PolynomialBound)
    (bounded : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (p n))
    (n : ℕ) (bits : BitString) (word : Word α) :
    (machine G p).Produces (generatorData n) bits word ↔
      G.machine.Produces (generatorData n) bits word :=
  (rejectDrain_produces_iff_of_timeBound (familyClock G.machine p) _ _
    (familyClock_timeBound G.machine p n) bits word).trans
      (clock_produces_iff G p bounded n bits word)

theorem generatedLanguage (G : UniformGenerators α) (p : PolynomialBound)
    (bounded : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (p n)) (n : ℕ) :
    (machine G p).generatedLanguage (generatorData n) = G.layer n := by
  ext word
  simp only [Machine.generatedLanguage, UniformGenerators.layer, Set.mem_ofPred_eq,
    produces_iff G p bounded n]

theorem finite_execution (G : UniformGenerators α) (p : PolynomialBound)
    (n : ℕ) (bits : BitString) :
    ∃ result, (machine G p).run (generatorData n) bits
      (polynomialClockTime p n + bits.length) = .halted (rejectDrainOutcome result) := by
  obtain ⟨result, source⟩ := familyClock_timeBound G.machine p n bits
  exact ⟨result, rejectDrain_run_halted (familyClock G.machine p) _ bits _ result source⟩

theorem full_trial (G : UniformGenerators α) (p : PolynomialBound)
    (bounded : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (p n))
    (n : ℕ) (bits : BitString) (length : bits.length = seed p n) :
    (machine G p).Accepts (generatorData n) bits ↔
      ((machine G p).generatedLanguage (generatorData n)).Nonempty := by
  constructor
  · exact fun accepted => (Machine.generatedLanguage_nonempty_iff_accepts _ _).mpr ⟨bits, accepted⟩
  · intro nonempty
    rw [generatedLanguage G p bounded n] at nonempty
    have long : p n < bits.length := by
      have lower := seed_lower p n
      omega
    obtain ⟨word, produced⟩ := G.machine.accepts_long_tape_of_acceptingTimeBound _ _
      (G.isGenerator n) (bounded n) bits long nonempty
    exact ⟨word, (produces_iff G p bounded n bits word).mpr produced⟩

theorem isGenerator (G : UniformGenerators α) (p : PolynomialBound)
    (bounded : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (p n)) (n : ℕ) :
    (machine G p).IsGenerator (generatorData n) := by
  apply Machine.isGenerator_of_full_trials _ _ (seed p n)
  · constructor
    · intro bits
      obtain ⟨result, terminal⟩ := finite_execution G p n bits
      exact ⟨_, _, terminal⟩
    · intro bits ticks rejected
      obtain ⟨result, terminal⟩ := finite_execution G p n bits
      have same := (machine G p).halted_outcome_unique _ bits ticks _ _ _ rejected terminal
      cases result <;> cases same
  · exact fun bits length => full_trial G p bounded n bits length

theorem trialBound (G : UniformGenerators α) (p : PolynomialBound)
    (bounded : ∀ n, G.machine.AcceptingTimeBound (generatorData n) (p n)) (n : ℕ) :
    (machine G p).TrialBound (generatorData n) (seed p n) (time p n) := by
  constructor
  · intro bits short
    obtain ⟨result, terminal⟩ := finite_execution G p n bits
    have cost : polynomialClockTime p n + bits.length ≤ time p n :=
      (Nat.add_le_add_left short _).trans ((polynomialClockTime p).add_le (seed p) n)
    exact (machine G p).haltsWithin_mono _ bits cost ⟨_, terminal⟩
  · exact fun bits length => full_trial G p bounded n bits length

/-- A source exact generator with the current paper's accepting-only runtime
bound has a language in the original native `PG` class. -/
theorem mem_pg (G : GeneratorFamily α) (bounded : G.toUniformGenerators.AcceptingPolynomialTime) :
    G.toUniformGenerators.language ∈ PG α := by
  obtain ⟨p, bound⟩ := bounded
  let H : GeneratorFamily α := {
    machine := machine G.toUniformGenerators p
    isGenerator := isGenerator G.toUniformGenerators p bound
    outputLength := by
      intro n word member
      change word ∈ (machine G.toUniformGenerators p).generatedLanguage (generatorData n) at member
      rw [generatedLanguage G.toUniformGenerators p bound n] at member
      exact G.outputLength n word member }
  refine ⟨H, ?_, seed p, time p, trialBound G.toUniformGenerators p bound⟩
  ext word
  change (∃ n, word ∈ (machine G.toUniformGenerators p).generatedLanguage (generatorData n)) ↔
    ∃ n, word ∈ G.toUniformGenerators.layer n
  simp only [generatedLanguage G.toUniformGenerators p bound]

end
end AcceptingTimeGeneration

/-- The retained native class agrees with the current paper's accepting-time
definition at polynomial bounds.  This is a proved compiler equivalence, not
a redefinition of `PG`. -/
theorem mem_pg_iff_accepting_polynomial_time {α : Type} [Fintype α] (L : Language α) :
    L ∈ PG α ↔ ∃ G : GeneratorFamily α,
      G.toUniformGenerators.language = L ∧ G.toUniformGenerators.AcceptingPolynomialTime := by
  constructor
  · rintro ⟨G, language, bounded⟩
    exact ⟨G, language, bounded.acceptingPolynomialTime⟩
  · rintro ⟨G, language, bounded⟩
    rw [← language]
    exact AcceptingTimeGeneration.mem_pg G bounded

/-- The paper's union-of-polynomial-time-bounds definition of PG agrees with
its retained trial-budget implementation. Empty layers need no accepting time. -/
theorem mem_pg_iff_exists_gtime_polynomial {α : Type} [Fintype α] (L : Language α) :
    L ∈ PG α ↔ ∃ p : PolynomialBound, L ∈ GTIME α p := by
  rw [mem_pg_iff_accepting_polynomial_time]
  constructor
  · rintro ⟨G, language, p, bound⟩
    exact ⟨p, G, language, bound⟩
  · rintro ⟨p, G, language, bound⟩
    exact ⟨G, language, p, bound⟩

end ComplexityOfGenerators
