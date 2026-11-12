import ComplexityOfGenerators.Examples.HAMPATHNative.Syntax
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def syntaxBudget (arguments : ℕ) : ℕ := 6 * arguments + 500 * (arguments + 1)^2 + 7

theorem syntaxCommand_runs (word : List Symbol) (auxiliary : List Unit) (bits : BitString) :
    ∃ ticks ≤ syntaxBudget (word.length + auxiliary.length), ∃ finalMemory,
      syntaxCommand.Runs 0 bits (loaded word auxiliary) ticks (.done finalMemory) ∧
        finalMemory.output = syntaxWord word := by
  obtain ⟨firstTicks, firstCost, first⟩ := prepare.runs (n := 0) bits (loaded word auxiliary) (by rfl)
  change prepare.command.Runs 0 bits (loaded word auxiliary) firstTicks (.done (prepared word auxiliary)) at first
  obtain ⟨parseTicks, parseCost, parseRun⟩ := (parser (O := Unit)).runs (n := 0) bits (prepared word auxiliary) (by rfl)
  let parsed : Memory Symbol Unit 32 :=
    {prepared word auxiliary with store := (parser (O := Unit)).eval (prepared word auxiliary).store}
  have parseBound := parser_cost (O := Unit) (prepared word auxiliary).store
    (word.length + auxiliary.length) (prepared_sizes word auxiliary)
  have firstBound : firstTicks ≤ 6 * word.length := by simpa [prepare, Routine.transfer, loaded] using firstCost
  change parseTicks ≤ (parser (O := Unit)).cost (prepared word auxiliary).store at parseCost
  obtain ⟨finishTicks, finishCost, finishRun⟩ := finish_runs bits parsed rfl
  have decisions := parser_decides (O := Unit) (prepared word auxiliary).store
  dsimp only at decisions
  rw [prepared_word] at decisions
  refine ⟨firstTicks + 1 + (parseTicks + 1 + finishTicks), ?_, _,
    Command.Runs.seq _ _ _ _ _ _ _ first (Command.Runs.seq _ _ _ _ _ _ _ parseRun finishRun), ?_⟩
  · unfold syntaxBudget
    omega
  · change [] ++ (if (((parsed.store 6).head?.isSome && (parsed.store 12).head?.isSome &&
      (parsed.store 2).isEmpty)) then [()] else []) = syntaxWord word
    rw [show ((parsed.store 6).head?.isSome && (parsed.store 12).head?.isSome &&
      (parsed.store 2).isEmpty) = wellFormed word from decisions]
    simp [syntaxWord]

theorem syntaxProgram_execution (word : List Symbol) (auxiliary : List Unit) (bits : BitString) :
    ∃ ticks ≤ syntaxBudget (word.length + auxiliary.length),
      syntaxProgram.Executes 0 bits ((loaded word auxiliary).at syntaxProgram.initial) ticks
        (.accepted (syntaxWord word)) := by
  obtain ⟨ticks, cost, finalMemory, run, output⟩ := syntaxCommand_runs word auxiliary bits
  have execution := Program.Evaluates.executes _ (run.compiled 0 (by rfl))
  change syntaxProgram.Executes 0 bits ((loaded word auxiliary).at syntaxProgram.initial) ticks
    (.accepted finalMemory.output) at execution
  rw [output] at execution
  exact ⟨ticks, cost, execution⟩

noncomputable def syntaxTime : PolynomialBound :=
  PolynomialBound.ofPolynomial (6 * Polynomial.X + 500 * (Polynomial.X + 1)^2 + 7)

theorem syntaxBudget_le (arguments : ℕ) : syntaxBudget arguments ≤ syntaxTime arguments := by
  apply (PolynomialBound.eval_le_ofPolynomial _ arguments).trans' ?_
  simp [syntaxBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

theorem syntaxMachine_runs (word : List Symbol) (auxiliary : List Unit) (bits : BitString) :
    ∃ ticks ≤ InputBank.compiledTime syntaxTime (word.length + auxiliary.length),
      syntaxMachine.run ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) bits ticks =
        .halted (.accepted (syntaxWord word)) := by
  obtain ⟨ticks, cost, execution⟩ := syntaxProgram_execution word auxiliary bits
  have loadedEq : InputBank.loadedMemory (0 : Fin 32) 1 (id : Symbol → Symbol) (fun (_ : Unit) => Symbol.bit false)
      ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) = loaded word auxiliary := by
    simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
  rw [← loadedEq] at execution
  obtain ⟨nativeTicks, nativeCost, native⟩ := InputBank.run_compiled syntaxProgram 0 1 id (fun _ => .bit false)
    (by decide) ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) bits ticks _ execution
  exact ⟨nativeTicks, nativeCost.trans (InputBank.compiledTime_bound syntaxTime _ ticks
    (cost.trans (syntaxBudget_le _))), native⟩

noncomputable def syntax_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => syntaxWord word) := by
  apply InputBank.polynomialWordFunction syntaxProgram 0 1 id (fun _ => .bit false)
    (by decide) (fun word _ => syntaxWord word) syntaxTime syntaxProgram_noRandom
  intro word auxiliary bits
  obtain ⟨ticks, cost, execution⟩ := syntaxProgram_execution word auxiliary bits
  refine ⟨ticks, cost.trans (syntaxBudget_le _), ?_⟩
  have loadedEq : InputBank.loadedMemory (0 : Fin 32) 1 (id : Symbol → Symbol) (fun (_ : Unit) => Symbol.bit false)
      ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) = loaded word auxiliary := by
    simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
  simpa only [loadedEq] using execution

end ComplexityOfGenerators.Examples.HAMPATH.Native
