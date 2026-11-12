import ComplexityOfGenerators.Examples.SATNative.VerifierBounds
import ComplexityOfGenerators.Simulation.WordStack.BooleanReturn
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native

/-! The concrete native deterministic SAT certificate verifier. False
certificates reach a genuine rejecting machine transition. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation.NativeVerifier

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] NativeEvaluation.verifier NativeEvaluation.prepareEvaluation
  NativeEvaluation.evaluationChoice NativeEvaluation.evaluationRoutine

def inputPrepare : Routine Symbol Unit 32 :=
  (Routine.transfer 0 2 (by decide) id).seq (Routine.transfer 1 3 (by decide) id)

noncomputable def routine : Routine Symbol Unit 32 := inputPrepare.seq NativeEvaluation.verifier

def checks : Program.BooleanChecks Symbol 32 :=
  ![(2, fun head => !head.isSome), (17, fun head => !head.isSome), (6, fun head => head.isSome)]

@[simp] theorem checksPass_eq (s : NativeEvaluation.Store) : Program.checksPass checks s = verdict s := by
  cases word : s 2 <;> simp [Program.checksPass, checks, verdict, word]

noncomputable def program := (routine.command.program 0).booleanReturn checks

noncomputable def machine : Machine Symbol Symbol Unit := InputBank.machine program 0 1 id id

def loaded (word certificate : List Symbol) : Memory Symbol Unit 32 :=
  ⟨(), 0, 0, [], Function.update (Function.update (fun _ => []) 0 word.reverse) 1 certificate.reverse⟩

def prepared (word certificate : List Symbol) : Memory Symbol Unit 32 :=
  {loaded word certificate with store := inputPrepare.eval (loaded word certificate).store}

theorem prepared_fields (word certificate : List Symbol) :
    (prepared word certificate).store 2 = word ∧ (prepared word certificate).store 3 = certificate ∧
      stackBound (word.length + certificate.length) (prepared word certificate).store := by
  refine ⟨?_, ?_, ?_⟩
  · simp [prepared, loaded, inputPrepare, Routine.seq, Routine.transfer]
  · simp [prepared, loaded, inputPrepare, Routine.seq, Routine.transfer]
  · intro j
    by_cases a : j = 0 <;> by_cases b : j = 1 <;> by_cases c : j = 2 <;> by_cases d : j = 3 <;>
      simp [prepared, loaded, inputPrepare, Routine.seq, Routine.transfer, a, b, c, d] <;> omega

noncomputable def primitiveBudget (arguments : ℕ) : ℕ :=
  8 * arguments + (NativeEvaluation.stepConstant + 400) * (arguments + 2)^2 + 10

set_option maxHeartbeats 1000000 in
theorem routine_cost (word certificate : List Symbol) :
    routine.cost (loaded word certificate).store + 3 ≤ primitiveBudget (word.length + certificate.length) := by
  have bounds := prepared_fields word certificate
  have cost := NativeEvaluation.verifier_cost (O := Unit) (prepared word certificate).store
    (word.length + certificate.length) bounds.2.2
  have preparation : inputPrepare.cost (loaded word certificate).store = 6 * word.length + 1 + 6 * certificate.length := by
    simp [inputPrepare, Routine.seq, Routine.transfer, loaded]
  change inputPrepare.cost (loaded word certificate).store + 1 +
    (NativeEvaluation.verifier (O := Unit)).cost (prepared word certificate).store + 3 ≤ _
  rw [preparation]
  unfold primitiveBudget
  omega

def outcome (word certificate : List Symbol) : Outcome Unit :=
  if verifies word certificate then .accepted [] else .rejected

set_option maxHeartbeats 1000000 in
theorem program_execution (word certificate : List Symbol) (bits : BitString) :
    ∃ ticks ≤ primitiveBudget (word.length + certificate.length),
      program.Executes 0 bits ((loaded word certificate).at program.initial) ticks (outcome word certificate) := by
  obtain ⟨ticks, cost, run⟩ := routine.runs (n := 0) bits (loaded word certificate) (by rfl)
  let final : Memory Symbol Unit 32 := {loaded word certificate with store := routine.eval (loaded word certificate).store}
  have source : (routine.command.program 0).Returns 0 bits (loaded word certificate) ticks final := run.compiled 0 (by rfl)
  obtain ⟨total, totalCost, execution⟩ := Program.returns_booleanReturn (routine.command.program 0) checks (by rfl) source
  have verdictEq : verdict final.store = verifies word certificate := by
    change verdict ((NativeEvaluation.verifier (O := Unit)).eval (prepared word certificate).store) = _
    have correctness := verifier_decides (O := Unit) (prepared word certificate).store
    have fields := prepared_fields word certificate
    simpa only [fields.1, fields.2.1] using correctness
  have output : final.output = [] := rfl
  rw [output] at execution
  have budget := routine_cost word certificate
  refine ⟨total, by omega, ?_⟩
  simpa only [program, Program.booleanReturn, checksPass_eq, verdictEq, outcome] using execution

noncomputable def primitiveTime : PolynomialBound := PolynomialBound.ofPolynomial
  (8 * Polynomial.X + Polynomial.C (NativeEvaluation.stepConstant + 400) * (Polynomial.X + 2)^2 + 10)

theorem primitiveBudget_le (arguments : ℕ) : primitiveBudget arguments ≤ primitiveTime arguments := by
  apply (PolynomialBound.eval_le_ofPolynomial _ arguments).trans' ?_
  simp [primitiveBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

theorem program_noRandom : InputBank.NoRandom program := by
  apply Program.booleanReturn_noRandom
  apply Command.RandomFree.noRandom
  simp [routine, inputPrepare]

theorem machine_deterministic : machine.Deterministic := InputBank.machine_deterministic program 0 1 id id program_noRandom

noncomputable def time : PolynomialBound := InputBank.compiledTime primitiveTime

theorem machine_runs (word certificate : List Symbol) (bits : BitString) :
    ∃ ticks ≤ time (word.length + certificate.length),
      machine.run ({input := word, auxiliary := certificate} : InputData Symbol Symbol) bits ticks =
        .halted (outcome word certificate) := by
  obtain ⟨ticks, cost, execution⟩ := program_execution word certificate bits
  have loadedEq : InputBank.loadedMemory (0 : Fin 32) 1 (id : Symbol → Symbol) (id : Symbol → Symbol)
      ({input := word, auxiliary := certificate} : InputData Symbol Symbol) = loaded word certificate := by
    simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
  rw [← loadedEq] at execution
  obtain ⟨nativeTicks, nativeCost, native⟩ := InputBank.run_compiled program 0 1 id id
    (by decide) ({input := word, auxiliary := certificate} : InputData Symbol Symbol) bits ticks _ execution
  exact ⟨nativeTicks, nativeCost.trans (InputBank.compiledTime_bound primitiveTime _ ticks (cost.trans (primitiveBudget_le _))), native⟩

theorem machine_time (word certificate : List Symbol) :
    machine.TimeBound ({input := word, auxiliary := certificate} : InputData Symbol Symbol)
      (time (word.length + certificate.length)) := by
  intro bits
  obtain ⟨ticks, bound, run⟩ := machine_runs word certificate bits
  have padded := machine.run_halted_add ({input := word, auxiliary := certificate} : InputData Symbol Symbol)
    bits ticks (outcome word certificate) run (time (word.length + certificate.length) - ticks)
  exact ⟨_, by simpa only [Nat.add_sub_of_le bound] using padded⟩

theorem machine_correct (word certificate : List Symbol) :
    machine.Accepts ({input := word, auxiliary := certificate} : InputData Symbol Symbol) [] ↔
      certificate ∈ wordCertificates word := by
  rw [← verifies_iff]
  obtain ⟨ticks, _, run⟩ := machine_runs word certificate []
  constructor
  · rintro ⟨output, otherTicks, accepted⟩
    have same := machine.halted_outcome_unique ({input := word, auxiliary := certificate} : InputData Symbol Symbol)
      [] ticks otherTicks (outcome word certificate) (.accepted output) run accepted
    cases result : verifies word certificate <;> simp [outcome, result] at same ⊢
  · intro good
    exact ⟨[], ticks, by simpa [outcome, good] using run⟩

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation.NativeVerifier
