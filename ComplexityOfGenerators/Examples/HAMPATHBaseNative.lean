import ComplexityOfGenerators.Examples.HAMPATHBaseGenerator

/-! The implemented HAMPATH base sampler, compiled to a native finite-tape
machine. It produces the singleton exactly at productive target lengths and
drains its finite random tape at every other index. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.BaseSearch

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

noncomputable def stackTime : PolynomialBound := PolynomialBound.ofPolynomial
  (17 * Polynomial.X + 18 + Polynomial.X *
    (120 * ((Polynomial.X + 1) ^ 2 + 3) + (Command.counterBudget square).asPolynomial + 4))

theorem stackTime_bound (n : ℕ) : searchBudget n + 13 ≤ stackTime n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (17 * Polynomial.X + 18 + Polynomial.X *
      (120 * ((Polynomial.X + 1) ^ 2 + 3) + (Command.counterBudget square).asPolynomial + 4)) n
  change _ ≤ stackTime n at bound
  convert bound using 1
  simp [searchBudget, bodyBudget, storeBudget, encodingLength,
    Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, PolynomialBound.asPolynomial_eval]
  ring

def program : Program baseCommand.Control Unit Symbol 12 := baseCommand.program 0

noncomputable def machine : Machine Unit Bool Symbol := program.machine

theorem machine_execution (n : ℕ) (bits : BitString) :
    ∃ ticks, machine.run (generatorData n) bits ticks = .halted (expectedOutcome n) := by
  obtain ⟨ticks, _, result, run, outcome⟩ := command_runs n bits
  obtain ⟨nativeTicks, _, native⟩ := program.run_compiled (run.executes 0)
  exact ⟨nativeTicks, by simpa only [machine, outcome] using native⟩

theorem machine_bounded (n : ℕ) (bits : BitString) (short : bits.length ≤ 1) :
    machine.HaltsWithin (generatorData n) bits (Program.compiledTime stackTime n) := by
  obtain ⟨ticks, cost, result, run, _⟩ := command_runs n bits
  have stackCost : ticks ≤ stackTime n := by
    have := stackTime_bound n
    omega
  obtain ⟨nativeTicks, nativeCost, native⟩ := program.run_compiled (run.executes 0)
  have totalCost := nativeCost.trans (Program.compiledTime_bound stackTime n ticks stackCost)
  exact machine.haltsWithin_mono (generatorData n) bits totalCost ⟨result.outcome, native⟩

theorem machine_accepts_iff (n : ℕ) (bits : BitString) :
    machine.Accepts (generatorData n) bits ↔ Productive n := by
  obtain ⟨ticks, reference⟩ := machine_execution n bits
  constructor
  · rintro ⟨word, time, accepted⟩
    have same := machine.halted_outcome_unique (generatorData n) bits time ticks _ _ accepted reference
    by_contra unproductive
    simp [expectedOutcome, unproductive] at same
  · intro productive
    exact ⟨singleton.encode 0, ticks, by simpa [expectedOutcome, productive] using reference⟩

theorem machine_language (n : ℕ) :
    machine.generatedLanguage (generatorData n) = {word | Productive n ∧ word = singleton.encode 0} := by
  ext word
  constructor
  · rintro ⟨bits, _, time, accepted⟩
    have productive := (machine_accepts_iff n bits).mp ⟨word, time, accepted⟩
    obtain ⟨ticks, reference⟩ := machine_execution n bits
    have same := machine.halted_outcome_unique (generatorData n) bits time ticks _ _ accepted reference
    exact ⟨productive, by simpa [expectedOutcome, productive] using same⟩
  · rintro ⟨productive, rfl⟩
    obtain ⟨ticks, execution⟩ := machine_execution n [false]
    exact ⟨[false], by decide, ticks, by simpa [expectedOutcome, productive] using execution⟩

theorem support_nonempty (n : ℕ) :
    (machine.generatedLanguage (generatorData n)).Nonempty ↔ Productive n := by
  rw [machine_language]
  exact ⟨fun ⟨_, productive, _⟩ => productive, fun productive => ⟨_, productive, rfl⟩⟩

theorem machine_halting (n : ℕ) : machine.HaltingTransducer (generatorData n) := by
  constructor
  · intro bits
    obtain ⟨ticks, execution⟩ := machine_execution n bits
    exact ⟨ticks, _, execution⟩
  · intro bits time rejected
    obtain ⟨ticks, execution⟩ := machine_execution n bits
    have same := machine.halted_outcome_unique (generatorData n) bits time ticks _ _ rejected execution
    by_cases productive : Productive n <;> simp [expectedOutcome, productive] at same

theorem machine_generator (n : ℕ) : machine.IsGenerator (generatorData n) := by
  apply machine.isGenerator_of_full_trials (generatorData n) 1 (machine_halting n)
  intro bits _
  rw [machine_accepts_iff, support_nonempty]

/-- This is a concrete native base family for the exact recursive HAMPATH
construction; the remaining verifier/reduction/inverse machines are separate. -/
noncomputable def base : UniformGenerators Symbol where
  machine := machine
  isGenerator := machine_generator

theorem base_language (n : ℕ) : base.layer n = selfReduction.bases n := by
  change machine.generatedLanguage (generatorData n) = _
  rw [machine_language, bases_productive]

theorem base_polynomialTime : base.PolynomialTime := by
  refine ⟨⟨1, 0, by omega⟩, Program.compiledTime stackTime, ?_⟩
  intro n
  change machine.GeneratorTimeBound (generatorData n) 1 (Program.compiledTime stackTime n)
  constructor
  · intro bits short
    exact machine_bounded n bits short
  · intro bits _
    rw [machine_accepts_iff, support_nonempty]

end ComplexityOfGenerators.Examples.HAMPATH.BaseSearch
