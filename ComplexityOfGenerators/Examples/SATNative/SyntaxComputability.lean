import ComplexityOfGenerators.Examples.SATNative.SyntaxMachine
import ComplexityOfGenerators.Examples.SATNative.ParserPure

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeParser

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem finish_randomFree : Command.RandomFree finish := by
  unfold finish
  apply Command.RandomFree.branch
  intro remaining
  split_ifs
  · exact .skip
  · apply Command.RandomFree.branch
    intro inside
    split_ifs
    · exact .skip
    · apply Command.RandomFree.branch
      intro valid
      split_ifs
      · exact Command.randomFree_emitFixed _ _
      · exact .skip

theorem syntaxProgram_noRandom : InputBank.NoRandom syntaxProgram := by
  apply Command.RandomFree.noRandom
  simp [syntaxCommand, prepare, finish_randomFree]

theorem syntaxMachine_deterministic : syntaxMachine.Deterministic :=
  InputBank.machine_deterministic syntaxProgram 0 1 id (fun _ => .zero) syntaxProgram_noRandom

/-- An actual deterministic polynomial word function, obtained from the
concrete finite native parser and its proved primitive executions. -/
noncomputable def syntax_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => syntaxWord word) := by
  apply InputBank.polynomialWordFunction syntaxProgram 0 1 id (fun _ => .zero)
    (by decide) (fun word _ => syntaxWord word) syntaxTime syntaxProgram_noRandom
  intro word auxiliary bits
  obtain ⟨ticks, cost, execution⟩ := syntaxProgram_execution word auxiliary bits
  refine ⟨ticks, cost.trans (syntaxBudget_le _), ?_⟩
  have loadedEq : InputBank.loadedMemory (0 : Fin 32) 1 (id : Symbol → Symbol) (fun (_ : Unit) => Symbol.zero)
      ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) = loaded word auxiliary := by
    simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
  simpa only [loadedEq] using execution

end ComplexityOfGenerators.Examples.PaddedCNF.NativeParser
