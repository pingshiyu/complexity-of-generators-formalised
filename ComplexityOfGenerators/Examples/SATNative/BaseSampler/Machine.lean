import ComplexityOfGenerators.Examples.SATNative.BaseSampler.Finish
import ComplexityOfGenerators.Proofs.CommandGenerators

/-! A concrete full-support polynomial generator for SAT's constant-formula
bases. Invalid proposals use the implemented length-specific default. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] NativeEvaluation.verifier check NativeEvaluation.stepConstant

def command : Code := prepare.seq (check.command.seq finish)

def primitiveBudget (n supplied : ℕ) : ℕ :=
  100*n+supplied+100+(NativeEvaluation.stepConstant+400)*(n+2)^2

def trialOutcome (n : ℕ) (bits : BitString) : Outcome Symbol :=
  if 4*n ≤ bits.length then
    expectedOutcome n (decodeWords n bits) (NativeEvaluation.verifies (decodeWords n bits) [])
  else .exhausted

theorem command_runs (n : ℕ) (bits : BitString) :
    ∃ ticks ≤ primitiveBudget n bits.length, ∃ result,
      command.Runs n bits Command.emptyMemory ticks result ∧ result.outcome = trialOutcome n bits := by
  by_cases enough : 4*n ≤ bits.length
  · obtain ⟨prepareTicks, prepareBound, prepareRun⟩ := prepare_full n bits enough
    let ready := preparedMemory n bits
    obtain ⟨checkTicks, checkBound, checkRun⟩ := check.runs (n := n) bits ready le_rfl
    let checked : Memory := {ready with store := check.eval ready.store}
    have cost := check_cost ready.store n (prepared_bound n bits)
    have word : checked.store 34 = decodeWords n bits := by
      rw [show checked.store 34 = check.eval ready.store 34 from rfl, check_frame _ _ (by decide)]
      simp [ready, preparedMemory, preparedStore]
    have counter : checked.store 32 = List.replicate n .zero := by
      rw [show checked.store 32 = check.eval ready.store 32 from rfl, check_frame _ _ (by decide)]
      simp [ready, preparedMemory, preparedStore]
    have empty : checked.store 33 = [] := by
      rw [show checked.store 33 = check.eval ready.store 33 from rfl, check_frame _ _ (by decide)]
      simp [ready, preparedMemory, preparedStore]
    obtain ⟨finishTicks, finishBound, result, finishRun, outcome⟩ := finish_runs n bits checked le_rfl
      (decodeWords n bits) (decodeWords_length _ _) word counter empty rfl
    have verdictEq : verdict checked.store = NativeEvaluation.verifies (decodeWords n bits) [] := by
      rw [show verdict checked.store = verdict (check.eval ready.store) from rfl, check_verdict]
      simp [ready, preparedMemory, preparedStore]
    have run := Command.Runs.seq _ _ _ _ _ _ _ prepareRun
      (Command.Runs.seq _ _ _ _ _ _ _ checkRun finishRun)
    refine ⟨prepareTicks+1+(checkTicks+1+finishTicks), ?_, result, run, ?_⟩
    · unfold primitiveBudget
      omega
    · simpa only [trialOutcome, enough, ite_true, verdictEq] using outcome
  · obtain ⟨ticks, bound, absent⟩ := prepare_short n bits (by omega)
    refine ⟨ticks, ?_, .exhausted,
      Command.Runs.seq_absent _ _ _ ticks absent, by simp [trialOutcome, enough, Result.outcome]⟩
    unfold primitiveBudget
    exact (show ticks ≤ 100*n+bits.length+100 by omega).trans (Nat.le_add_right _ _)


def program : Program command.Control Symbol Symbol 35 := command.program 0

noncomputable def machine : Machine Unit Bool Symbol := program.machine

theorem machine_execution (n : ℕ) (bits : BitString) :
    ∃ ticks, machine.run (generatorData n) bits ticks = .halted (trialOutcome n bits) := by
  obtain ⟨ticks, _, result, run, outcome⟩ := command_runs n bits
  obtain ⟨nativeTicks, _, native⟩ := program.run_compiled (run.executes 0)
  exact ⟨nativeTicks, by simpa only [machine, outcome] using native⟩

def seed : PolynomialBound := ⟨4, 1, by decide⟩

noncomputable def primitiveTime : PolynomialBound := PolynomialBound.ofPolynomial
  (100*Polynomial.X+seed.asPolynomial+100+
    Polynomial.C (NativeEvaluation.stepConstant+400)*(Polynomial.X+2)^2)

theorem primitiveBudget_le (n supplied : ℕ) (short : supplied ≤ seed n) :
    primitiveBudget n supplied ≤ primitiveTime n := by
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_pow, PolynomialBound.asPolynomial_eval]
  unfold primitiveBudget
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_left short (100*n)) 100) _

noncomputable def time : PolynomialBound := Program.compiledTime primitiveTime

theorem machine_bounded (n : ℕ) (bits : BitString) (short : bits.length ≤ seed n) :
    machine.HaltsWithin (generatorData n) bits (time n) := by
  obtain ⟨ticks, bound, result, run, _⟩ := command_runs n bits
  have primitiveCost := bound.trans (primitiveBudget_le n bits.length short)
  obtain ⟨nativeTicks, nativeCost, native⟩ := program.run_compiled (run.executes 0)
  have totalCost := nativeCost.trans (Program.compiledTime_bound primitiveTime n ticks primitiveCost)
  exact machine.haltsWithin_mono (generatorData n) bits totalCost ⟨result.outcome, native⟩

end
end ComplexityOfGenerators.Examples.PaddedCNF.BaseSampler
