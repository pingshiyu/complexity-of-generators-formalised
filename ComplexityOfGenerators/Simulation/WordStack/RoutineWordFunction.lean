import ComplexityOfGenerators.Simulation.WordStack.RandomFree
import ComplexityOfGenerators.Simulation.WordStack.Output

namespace ComplexityOfGenerators.Simulation.WordStack.Routine

set_option backward.isDefEq.respectTransparency false

variable {I A S O : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype S] [Fintype O]

def wordCommand (routine : Routine S O k) (output : Fin k) (decode : S → Option O) : Command S O k :=
  routine.command.seq (Command.emitWord output decode)

/-- Compile an actual finite routine followed by a stored-word emitter. Both
input loading and primitive output steps are included in the polynomial clock. -/
noncomputable def polynomialWordFunction (routine : Routine S O k)
    (inputStack auxiliaryStack idle output : Fin k) (different : inputStack ≠ auxiliaryStack)
    (encodeInput : I → S) (encodeAuxiliary : A → S) (decode : S → Option O)
    (function : List I → List A → List O) (time : PolynomialBound)
    (pure : Command.RandomFree routine.command)
    (computes : ∀ input auxiliary,
      (routine.eval (InputBank.loadedMemory (O := O) inputStack auxiliaryStack encodeInput encodeAuxiliary
        ({input := input, auxiliary := auxiliary} : InputData I A)).store output).filterMap decode = function input auxiliary)
    (bounded : ∀ input auxiliary,
      let store := (InputBank.loadedMemory (O := O) inputStack auxiliaryStack encodeInput encodeAuxiliary
        ({input := input, auxiliary := auxiliary} : InputData I A)).store
      routine.cost store + 1 + 4 * (routine.eval store output).length ≤ time (input.length + auxiliary.length)) :
    PolynomialWordFunction function := by
  let code := wordCommand routine output decode
  let program := code.program idle
  apply InputBank.polynomialWordFunction program inputStack auxiliaryStack encodeInput encodeAuxiliary
    different function time (Command.RandomFree.noRandom (.seq pure (Command.randomFree_emitWord output decode)) idle)
  intro input auxiliary bits
  let memory : Memory S O k := InputBank.loadedMemory inputStack auxiliaryStack encodeInput encodeAuxiliary
    ({input := input, auxiliary := auxiliary} : InputData I A)
  obtain ⟨ticks, cost, run⟩ := routine.runs (n := 0) bits memory (by rfl)
  let after : Memory S O k := {memory with store := routine.eval memory.store}
  have outputRun := Command.emitWord_runs output decode bits after (by rfl : after.indexHead ≤ 0)
  have sequence := Command.Runs.seq memory after routine.command (Command.emitWord output decode)
    ticks (4 * (after.store output).length) _ run outputRun
  have execution := Program.Evaluates.executes _ (sequence.compiled idle (by rfl))
  change program.Executes 0 bits (memory.at program.initial) (ticks + 1 + 4 * (after.store output).length)
    (.accepted (Command.emitted output decode after).output) at execution
  have result : (Command.emitted output decode after).output = function input auxiliary := by
    simpa [Command.emitted, after, memory, InputBank.loadedMemory] using computes input auxiliary
  rw [result] at execution
  refine ⟨_, ?_, execution⟩
  exact (Nat.add_le_add_right (Nat.add_le_add_right cost 1) _).trans (bounded input auxiliary)

end ComplexityOfGenerators.Simulation.WordStack.Routine
