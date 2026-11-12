import ComplexityOfGenerators.Examples.SATNative.ParserBounds
import ComplexityOfGenerators.Simulation.WordStack.InputBank.Native
import ComplexityOfGenerators.Simulation.WordStack.FixedOutput

/-! A concrete native machine deciding the padded-CNF syntax relation. This
is shared parser machinery for SAT's verifier and substitution transducer; it
does not assert that the still unfinished SAT recursive-generator instance is
complete. All loading, parsing and output costs are charged below. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeParser

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

def syntaxWord (word : List Symbol) : List Unit := if (decode word).isSome then [()] else []

def prepare : Routine Symbol Unit 32 := Routine.transfer 0 2 (by decide) id

def finish : Command Symbol Unit 32 :=
  .branch 2 fun remaining => if remaining.1.isSome then .skip else
    .branch 17 fun inside => if inside.1.isSome then .skip else
      .branch 6 fun valid => if valid.1.isSome then Command.emitFixed 0 [()] else .skip

noncomputable def syntaxCommand : Command Symbol Unit 32 := prepare.command.seq (parser.command.seq finish)

noncomputable def syntaxProgram := syntaxCommand.program 0

noncomputable def syntaxMachine : Machine Symbol Unit Unit :=
  InputBank.machine syntaxProgram 0 1 id (fun _ => .zero)

def loaded (word : List Symbol) (auxiliary : List Unit) : Memory Symbol Unit 32 :=
  ⟨(), 0, 0, [], Function.update (Function.update (fun _ => []) 0 word.reverse) 1
    (auxiliary.reverse.map (fun _ => .zero))⟩

def prepared (word : List Symbol) (auxiliary : List Unit) : Memory Symbol Unit 32 :=
  {loaded word auxiliary with store := prepare.eval (loaded word auxiliary).store}

theorem prepared_word (word : List Symbol) (auxiliary : List Unit) :
    (prepared word auxiliary).store 2 = word := by
  simp [prepared, loaded, prepare, Routine.transfer]

theorem prepared_sizes (word : List Symbol) (auxiliary : List Unit) :
    stackBound (word.length + auxiliary.length) (prepared word auxiliary).store := by
  intro j
  by_cases source : j = 0 <;> by_cases input : j = 2 <;> by_cases aux : j = 1 <;>
    simp [prepared, loaded, prepare, Routine.transfer, source, input, aux] <;> omega

theorem finish_runs (bits : BitString) (m : Memory Symbol Unit 32) (index : m.indexHead = 0) :
    ∃ ticks ≤ 5, finish.Runs 0 bits m ticks
      (.done {m with output := m.output ++
        (if (m.store 2).isEmpty && !(m.store 17).head?.isSome && (m.store 6).head?.isSome then [()] else [])}) := by
  by_cases remaining : (m.store 2).head?.isSome = true
  · have nonempty : (m.store 2).isEmpty = false := by
      cases word : m.store 2 with
      | nil => simp [word] at remaining
      | cons head rest => rfl
    refine ⟨1, by omega, ?_⟩
    apply Command.Runs.branch m 2 _ 0 _
    simp [finish, observe, remaining, nonempty]
    exact Command.Runs.skip m
  · have empty : m.store 2 = [] := by
      cases word : m.store 2 with
      | nil => rfl
      | cons head rest => simp [word] at remaining
    by_cases inside : (m.store 17).head?.isSome = true
    · refine ⟨2, by omega, ?_⟩
      apply Command.Runs.branch m 2 _ 1 _
      simp only [finish, observe, empty, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
      apply Command.Runs.branch m 17 _ 0 _
      simp [observe, inside]
      exact Command.Runs.skip m
    · by_cases valid : (m.store 6).head?.isSome = true
      · refine ⟨5, by omega, ?_⟩
        apply Command.Runs.branch m 2 _ 4 _
        simp only [finish, observe, empty, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
        apply Command.Runs.branch m 17 _ 3 _
        simp only [observe, show (m.store 17).head?.isSome = false by cases flag : (m.store 17).head?.isSome <;> simp_all,
          Bool.false_eq_true, ite_false]
        apply Command.Runs.branch m 6 _ 2 _
        simp only [observe, valid, ite_true]
        simpa [empty, inside, valid] using Command.emitFixed_runs (0 : Fin 32) [()] bits m (by omega)
      · refine ⟨3, by omega, ?_⟩
        apply Command.Runs.branch m 2 _ 2 _
        simp only [finish, observe, empty, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
        apply Command.Runs.branch m 17 _ 1 _
        simp only [observe, show (m.store 17).head?.isSome = false by cases flag : (m.store 17).head?.isSome <;> simp_all,
          Bool.false_eq_true, ite_false]
        apply Command.Runs.branch m 6 _ 0 _
        simp [observe, valid, empty, inside]
        exact Command.Runs.skip m

noncomputable def syntaxBudget (arguments : ℕ) : ℕ :=
  6 * arguments + (stepConstant + 120) * (arguments + 2)^2 + 7

set_option maxHeartbeats 1000000 in
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
  · change [] ++ (if ((parsed.store 2).isEmpty && !(parsed.store 17).head?.isSome &&
      (parsed.store 6).head?.isSome) then [()] else []) = syntaxWord word
    rw [show ((parsed.store 2).isEmpty && !(parsed.store 17).head?.isSome &&
      (parsed.store 6).head?.isSome) = (decode word).isSome by exact decisions]
    simp [syntaxWord]

theorem syntaxProgram_execution (word : List Symbol) (auxiliary : List Unit) (bits : BitString) :
    ∃ ticks ≤ syntaxBudget (word.length + auxiliary.length),
      syntaxProgram.Executes 0 bits ((loaded word auxiliary).at syntaxProgram.initial) ticks (.accepted (syntaxWord word)) := by
  obtain ⟨ticks, cost, finalMemory, run, output⟩ := syntaxCommand_runs word auxiliary bits
  have execution := Program.Evaluates.executes _ (run.compiled 0 (by rfl))
  change syntaxProgram.Executes 0 bits ((loaded word auxiliary).at syntaxProgram.initial) ticks
    (.accepted finalMemory.output) at execution
  rw [output] at execution
  exact ⟨ticks, cost, execution⟩

noncomputable def syntaxTime : PolynomialBound := PolynomialBound.ofPolynomial
  (6 * Polynomial.X + Polynomial.C (stepConstant + 120) * (Polynomial.X + 2)^2 + 7)

theorem syntaxBudget_le (arguments : ℕ) : syntaxBudget arguments ≤ syntaxTime arguments := by
  apply (PolynomialBound.eval_le_ofPolynomial _ arguments).trans' ?_
  simp [syntaxBudget, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow]

theorem syntaxMachine_runs (word : List Symbol) (auxiliary : List Unit) (bits : BitString) :
    ∃ ticks ≤ InputBank.compiledTime syntaxTime (word.length + auxiliary.length),
      syntaxMachine.run ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) bits ticks =
        .halted (.accepted (syntaxWord word)) := by
  obtain ⟨ticks, cost, execution⟩ := syntaxProgram_execution word auxiliary bits
  have loadedEq : InputBank.loadedMemory (0 : Fin 32) 1 (id : Symbol → Symbol) (fun (_ : Unit) => Symbol.zero)
      ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) = loaded word auxiliary := by
    simp [InputBank.loadedMemory, InputBank.auxiliaryStore, InputBank.inputStore, loaded]
  rw [← loadedEq] at execution
  obtain ⟨nativeTicks, nativeCost, native⟩ := InputBank.run_compiled syntaxProgram 0 1 id (fun _ => .zero)
    (by decide) ({input := word, auxiliary := auxiliary} : InputData Symbol Unit) bits ticks _ execution
  exact ⟨nativeTicks, nativeCost.trans (InputBank.compiledTime_bound syntaxTime _ ticks (cost.trans (syntaxBudget_le _))), native⟩

end ComplexityOfGenerators.Examples.PaddedCNF.NativeParser
