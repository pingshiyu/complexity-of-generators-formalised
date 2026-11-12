import ComplexityOfGenerators.Examples.SATNative.SubstitutionCorrect
import ComplexityOfGenerators.Simulation.WordStack.Output

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency true

def bufferRoutine : Routine Symbol Symbol 32 :=
  (Routine.clear 28).seq (Routine.transfer 21 28 (by decide) id)

def emitBuffer : Command Symbol Symbol 32 := bufferRoutine.command.seq (Command.emitWord 28 some)

theorem bufferRoutine_eval (s : Store) :
    bufferRoutine.eval s = Function.update (Function.update s 21 []) 28 (s 21).reverse := by
  funext j
  by_cases a : j = 21 <;> by_cases b : j = 28 <;> simp [bufferRoutine, Routine.seq, Routine.clear, Routine.transfer, a, b]

theorem bufferRoutine_cost (s : Store) : bufferRoutine.cost s = 3 * (s 28).length + 1 + 6 * (s 21).length := by
  simp [bufferRoutine, Routine.seq, Routine.clear, Routine.transfer]

theorem emitBuffer_runs {n : ℕ} (bits : BitString) (m : Memory Symbol Symbol 32) (bounded : m.indexHead ≤ n) :
    ∃ ticks ≤ 3 * (m.store 28).length + 10 * (m.store 21).length + 2, ∃ final,
      emitBuffer.Runs n bits m ticks (.done final) ∧ final.output = m.output ++ (m.store 21).reverse := by
  obtain ⟨ticks, cost, first⟩ := bufferRoutine.runs bits m bounded
  let middle : Memory Symbol Symbol 32 := {m with store := bufferRoutine.eval m.store}
  have last := Command.emitWord_runs (28 : Fin 32) (some : Symbol → Option Symbol) bits middle bounded
  have size : (middle.store 28).length = (m.store 21).length := by simp [middle, bufferRoutine_eval]
  refine ⟨ticks + 1 + 4 * (middle.store 28).length, ?_, _, Command.Runs.seq _ _ _ _ _ _ _ first last, ?_⟩
  · rw [size]
    rw [bufferRoutine_cost] at cost
    omega
  · simp [Command.emitted, middle, bufferRoutine_eval]

def finishCommand : Command Symbol Symbol 32 :=
  .branch 2 fun remaining => if remaining.1.isSome then .skip else
    .branch 17 fun inside => if inside.1.isSome then .skip else
      .branch 6 fun valid => if valid.1.isSome then emitBuffer else .skip

theorem finishCommand_runs {n : ℕ} (bits : BitString) (m : Memory Symbol Symbol 32) (bounded : m.indexHead ≤ n) :
    ∃ ticks ≤ 3 * (m.store 28).length + 10 * (m.store 21).length + 5, ∃ final,
      finishCommand.Runs n bits m ticks (.done final) ∧
        final.output = m.output ++ (if NativeEvaluation.verdict m.store then (m.store 21).reverse else []) := by
  cases remaining : m.store 2 with
  | cons head rest =>
    refine ⟨1, by omega, m, ?_, ?_⟩
    · apply Command.Runs.branch m 2 _ 0 _
      simpa [finishCommand, observe, remaining] using Command.Runs.skip (n := n) (bits := bits) m
    · simp [NativeEvaluation.verdict, remaining]
  | nil =>
    cases inside : m.store 17 with
    | cons head rest =>
      refine ⟨2, by omega, m, ?_, ?_⟩
      · apply Command.Runs.branch m 2 _ 1 _
        simp only [observe, remaining, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
        apply Command.Runs.branch m 17 _ 0 _
        simpa [observe, inside] using Command.Runs.skip (n := n) (bits := bits) m
      · simp [NativeEvaluation.verdict, remaining, inside]
    | nil =>
      cases valid : m.store 6 with
      | nil =>
        refine ⟨3, by omega, m, ?_, ?_⟩
        · apply Command.Runs.branch m 2 _ 2 _
          simp only [observe, remaining, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
          apply Command.Runs.branch m 17 _ 1 _
          simp only [observe, inside, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
          apply Command.Runs.branch m 6 _ 0 _
          simpa [observe, valid] using Command.Runs.skip (n := n) (bits := bits) m
        · simp [NativeEvaluation.verdict, remaining, inside, valid]
      | cons head rest =>
        obtain ⟨ticks, cost, final, emitted, output⟩ := emitBuffer_runs bits m bounded
        refine ⟨1 + (1 + (1 + ticks)), by omega, final, ?_, ?_⟩
        · apply Command.Runs.branch m 2 _ (1 + (1 + ticks)) _
          simp only [observe, remaining, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
          apply Command.Runs.branch m 17 _ (1 + ticks) _
          simp only [observe, inside, List.head?_nil, Option.isSome_none, Bool.false_eq_true, ite_false]
          apply Command.Runs.branch m 6 _ ticks _
          simpa [observe, valid] using emitted
        · simpa [NativeEvaluation.verdict, remaining, inside, valid] using output

@[simp] theorem bufferRoutine_randomFree : Command.RandomFree bufferRoutine.command := by simp [bufferRoutine]

@[simp] theorem emitBuffer_randomFree : Command.RandomFree emitBuffer := by simp [emitBuffer]

@[simp] theorem finishCommand_randomFree : Command.RandomFree finishCommand := by
  unfold finishCommand
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
      split_ifs <;> simp

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
