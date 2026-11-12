import ComplexityOfGenerators.Examples.SATNative.SubstitutionOutput
import ComplexityOfGenerators.Examples.SATNative.SubstitutionBounds
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native

/-! The actual deterministic native word transducer for SAT's checked
substitution. Every input pair, including malformed words and labels, is
covered by the output equation and polynomial execution bound. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution.NativeReduction

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency true

attribute [local irreducible] checkedStream

def inputPrepare : Routine Symbol Symbol 32 :=
  (Routine.transfer 0 2 (by decide) id).seq (Routine.transfer 1 3 (by decide) id)

noncomputable def command : Command Symbol Symbol 32 :=
  inputPrepare.command.seq ((checkedStream (O := Symbol)).command.seq finishCommand)

noncomputable def program := command.program 0

noncomputable def machine : Machine Symbol Symbol Symbol := InputBank.machine program 0 1 id id

def loaded (word label : List Symbol) : Memory Symbol Symbol 32 :=
  ⟨(), 0, 0, [], Function.update (Function.update (fun _ => []) 0 word.reverse) 1 label.reverse⟩

def prepared (word label : List Symbol) : Memory Symbol Symbol 32 :=
  {loaded word label with store := inputPrepare.eval (loaded word label).store}

theorem prepared_fields (word label : List Symbol) :
    (prepared word label).store 2 = word ∧ (prepared word label).store 3 = label ∧
      stackBound (word.length + label.length) (prepared word label).store := by
  refine ⟨?_, ?_, ?_⟩
  · simp [prepared, loaded, inputPrepare, Routine.seq, Routine.transfer]
  · simp [prepared, loaded, inputPrepare, Routine.seq, Routine.transfer]
  · intro j
    by_cases a : j = 0 <;> by_cases b : j = 1 <;> by_cases c : j = 2 <;> by_cases d : j = 3 <;>
      simp [prepared, loaded, inputPrepare, Routine.seq, Routine.transfer, a, b, c, d] <;> omega

noncomputable def primitiveBudget (arguments : ℕ) : ℕ :=
  8 * arguments + checkedStreamTime arguments + 14 * (arguments + 2)^2 + 20

set_option maxHeartbeats 1000000 in
theorem command_runs (word label : List Symbol) (bits : BitString) :
    ∃ ticks ≤ primitiveBudget (word.length + label.length), ∃ final,
      command.Runs 0 bits (loaded word label) ticks (.done final) ∧ final.output = wordReduce word label := by
  obtain ⟨firstTicks, firstCost, first⟩ := inputPrepare.runs (n := 0) bits (loaded word label) (by rfl)
  change inputPrepare.command.Runs 0 bits (loaded word label) firstTicks (.done (prepared word label)) at first
  obtain ⟨streamTicks, streamCost, streamRun⟩ := (checkedStream (O := Symbol)).runs (n := 0) bits (prepared word label) (by rfl)
  let parsed : Memory Symbol Symbol 32 :=
    {prepared word label with store := (checkedStream (O := Symbol)).eval (prepared word label).store}
  have fields := prepared_fields word label
  have streamBound := checkedStream_bound (O := Symbol) (prepared word label).store
    (word.length + label.length) fields.2.2
  have sourceTime := checkedStream_cost (O := Symbol) (prepared word label).store
    (word.length + label.length) fields.2.2
  have firstBound : firstTicks ≤ 6 * word.length + 1 + 6 * label.length := by
    simpa [inputPrepare, Routine.seq, Routine.transfer, loaded] using firstCost
  change streamTicks ≤ (checkedStream (O := Symbol)).cost (prepared word label).store at streamCost
  obtain ⟨finishTicks, finishCost, final, finishRun, output⟩ := finishCommand_runs bits parsed (by rfl)
  have bufferBound := streamBound 21
  have scratchBound := streamBound 28
  change (parsed.store 21).length ≤ (word.length + label.length + 2)^2 at bufferBound
  change (parsed.store 28).length ≤ (word.length + label.length + 2)^2 at scratchBound
  refine ⟨firstTicks + 1 + (streamTicks + 1 + finishTicks), ?_, final,
    Command.Runs.seq _ _ _ _ _ _ _ first (Command.Runs.seq _ _ _ _ _ _ _ streamRun finishRun), ?_⟩
  · unfold primitiveBudget
    omega
  · have correctness := streamOutput_correct (prepared word label).store
    rw [fields.1, fields.2.1] at correctness
    have returned : final.output = streamOutput (prepared word label).store := by
      simpa only [parsed, streamOutput, prepared, loaded, List.nil_append] using output
    exact returned.trans correctness

theorem program_execution (word label : List Symbol) (bits : BitString) :
    ∃ ticks ≤ primitiveBudget (word.length + label.length),
      program.Executes 0 bits ((loaded word label).at program.initial) ticks (.accepted (wordReduce word label)) := by
  obtain ⟨ticks, cost, final, run, output⟩ := command_runs word label bits
  have execution := Program.Evaluates.executes _ (run.compiled 0 (by rfl))
  change program.Executes 0 bits ((loaded word label).at program.initial) ticks (.accepted final.output) at execution
  rw [output] at execution
  exact ⟨ticks, cost, execution⟩

noncomputable def primitiveTime : PolynomialBound := PolynomialBound.ofPolynomial
  (8 * Polynomial.X + checkedStreamTime.asPolynomial + 14 * (Polynomial.X + 2)^2 + 20)

theorem primitiveBudget_le (arguments : ℕ) : primitiveBudget arguments ≤ primitiveTime arguments := by
  apply (PolynomialBound.eval_le_ofPolynomial _ arguments).trans' ?_
  simp [primitiveBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow,
    PolynomialBound.asPolynomial_eval]

theorem program_noRandom : InputBank.NoRandom program := by
  apply Command.RandomFree.noRandom
  simp [command, inputPrepare]

theorem machine_deterministic : machine.Deterministic := InputBank.machine_deterministic program 0 1 id id program_noRandom

/-- The completed computational field for the manuscript's checked SAT
self-reduction, using the actual native machine above. -/
noncomputable def computable : PolynomialWordFunction wordReduce := by
  apply InputBank.polynomialWordFunction program 0 1 id id (by decide) wordReduce primitiveTime program_noRandom
  intro word label bits
  obtain ⟨ticks, cost, execution⟩ := program_execution word label bits
  refine ⟨ticks, cost.trans (primitiveBudget_le _), ?_⟩
  have loadedEq : InputBank.loadedMemory (0 : Fin 32) 1 (id : Symbol → Symbol) (id : Symbol → Symbol)
      ({input := word, auxiliary := label} : InputData Symbol Symbol) = loaded word label := by
    simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
  simpa only [loadedEq] using execution

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution.NativeReduction
