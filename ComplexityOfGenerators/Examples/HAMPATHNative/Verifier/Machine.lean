import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Controller
import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.LoopBounds
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native

/-! A concrete native deterministic verifier for all HAMPATH certificate
words. Invalid certificates terminate with a rejecting transition. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] loop body

noncomputable def program := (routine.command.program 0).booleanReturn checks

noncomputable def machine : Machine Symbol Symbol Unit := InputBank.machine program 0 1 id id

def primitiveBudget (n : ℕ) : ℕ := n*(stepBudget n+5)+100*(workspace n+n+1)

theorem routine_cost (word certificate : List Symbol) :
    routine.cost (loaded word certificate).store + 3 ≤ primitiveBudget (word.length+certificate.length) := by
  let n := word.length+certificate.length
  let a := prepared word certificate
  let b := loop.eval a
  obtain ⟨current, remaining, clock, small⟩ := prepared_fields word certificate
  change a 32 = word at current
  change a 33 = certificate at remaining
  change (a 34).length = certificate.length at clock
  have room : n ≤ workspace n := by unfold workspace; omega
  have aBound : StoreBound a (workspace n) := small.mono room
  have currentBound : (a 32).length ≤ n := by rw [current]; dsimp [n]; omega
  have remainingBound : (a 33).length ≤ n := by rw [remaining]; dsimp [n]; omega
  have clockBound : (a 34).length ≤ n := by rw [clock]; dsimp [n]; omega
  obtain ⟨bBound, bCost⟩ := loop_bound a n aBound currentBound remainingBound clockBound
  have workspacePositive : 1 ≤ workspace n := by unfold workspace; omega
  obtain ⟨_, last⟩ := baseTest_bound b (workspace n) workspacePositive bBound
  have first : inputPrepare.cost (loaded word certificate).store = 6*word.length+20*certificate.length+5 := by
    simp [inputPrepare, loaded, Routine.seq, Routine.transfer, Routine.assign_cost, List.length_reverse]
    omega
  change inputPrepare.cost (loaded word certificate).store+1+(loop.cost a+1+baseTest.cost b)+3 ≤ _
  rw [first]
  unfold primitiveBudget
  dsimp only [n] at *
  omega

def outcome (word certificate : List Symbol) : Outcome Unit :=
  if value word certificate then .accepted [] else .rejected

theorem program_execution (word certificate : List Symbol) (bits : BitString) :
    ∃ ticks ≤ primitiveBudget (word.length+certificate.length),
      program.Executes 0 bits ((loaded word certificate).at program.initial) ticks (outcome word certificate) := by
  obtain ⟨ticks, cost, run⟩ := routine.runs (n := 0) bits (loaded word certificate) (by rfl)
  let final : Memory Symbol Unit 64 := {loaded word certificate with store := routine.eval (loaded word certificate).store}
  have source : (routine.command.program 0).Returns 0 bits (loaded word certificate) ticks final := run.compiled 0 (by rfl)
  obtain ⟨total, totalCost, execution⟩ := Program.returns_booleanReturn (routine.command.program 0) checks (by rfl) source
  have verdict : Program.checksPass checks final.store = value word certificate := routine_decides word certificate
  have output : final.output = [] := rfl
  rw [output] at execution
  have budget := routine_cost word certificate
  refine ⟨total, by omega, ?_⟩
  simpa only [program, Program.booleanReturn, verdict, outcome] using execution

noncomputable def primitiveTime : PolynomialBound := PolynomialBound.ofPolynomial
  (Polynomial.X*(500000000*(Polynomial.X+3)^2+5)+100*(1000*(2*Polynomial.X+3)+Polynomial.X+1))

theorem primitiveBudget_le (n : ℕ) : primitiveBudget n ≤ primitiveTime n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp [primitiveBudget, stepBudget, workspace, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

theorem program_noRandom : InputBank.NoRandom program := by
  apply Program.booleanReturn_noRandom
  apply Command.RandomFree.noRandom
  exact .seq (by simp [inputPrepare]) (.seq loop_randomFree baseTest_randomFree)

theorem machine_deterministic : machine.Deterministic := InputBank.machine_deterministic program 0 1 id id program_noRandom

noncomputable def time : PolynomialBound := InputBank.compiledTime primitiveTime

theorem machine_runs (word certificate : List Symbol) (bits : BitString) :
    ∃ ticks ≤ time (word.length+certificate.length),
      machine.run ({input := word, auxiliary := certificate} : InputData Symbol Symbol) bits ticks =
        .halted (outcome word certificate) := by
  obtain ⟨ticks, cost, execution⟩ := program_execution word certificate bits
  have loadedEq : InputBank.loadedMemory (0 : Fin 64) 1 (id : Symbol → Symbol) (id : Symbol → Symbol)
      ({input := word, auxiliary := certificate} : InputData Symbol Symbol) = loaded word certificate := by
    simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
  rw [← loadedEq] at execution
  obtain ⟨nativeTicks, nativeCost, native⟩ := InputBank.run_compiled program 0 1 id id
    (by decide) ({input := word, auxiliary := certificate} : InputData Symbol Symbol) bits ticks _ execution
  exact ⟨nativeTicks, nativeCost.trans (InputBank.compiledTime_bound primitiveTime _ ticks (cost.trans (primitiveBudget_le _))), native⟩

theorem machine_time (word certificate : List Symbol) :
    machine.TimeBound ({input := word, auxiliary := certificate} : InputData Symbol Symbol)
      (time (word.length+certificate.length)) := by
  intro bits
  obtain ⟨ticks, bound, run⟩ := machine_runs word certificate bits
  have padded := machine.run_halted_add ({input := word, auxiliary := certificate} : InputData Symbol Symbol)
    bits ticks (outcome word certificate) run (time (word.length+certificate.length)-ticks)
  exact ⟨_, by simpa only [Nat.add_sub_of_le bound] using padded⟩

theorem machine_correct (word certificate : List Symbol) :
    machine.Accepts ({input := word, auxiliary := certificate} : InputData Symbol Symbol) [] ↔
      certificate ∈ wordCertificates word := by
  rw [← value_iff_certificate]
  obtain ⟨ticks, _, run⟩ := machine_runs word certificate []
  constructor
  · rintro ⟨output, otherTicks, accepted⟩
    have same := machine.halted_outcome_unique ({input := word, auxiliary := certificate} : InputData Symbol Symbol)
      [] ticks otherTicks (outcome word certificate) (.accepted output) run accepted
    cases result : value word certificate <;> simp [outcome, result] at same ⊢
  · intro good
    exact ⟨[], ticks, by simpa [outcome, good] using run⟩

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
