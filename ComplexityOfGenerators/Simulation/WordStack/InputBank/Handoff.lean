import ComplexityOfGenerators.Simulation.WordStack.InputBank.Load
import ComplexityOfGenerators.Simulation.WordStack.Execution

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank

open TransducerBank

set_option backward.isDefEq.respectTransparency false

variable {I A Q S O : Type} {k : ℕ} (P : Program Q S O k)
    (inputStack auxiliaryStack : Fin k) (encodeInput : I → S) (encodeAuxiliary : A → S)

def loadedMemory (data : InputData I A) : Memory S O k :=
  ⟨(), 0, 0, [], auxiliaryStore inputStack auxiliaryStack encodeInput encodeAuxiliary data data.auxiliary.length⟩

theorem input_initial (data : InputData I A) : inputState (O := O) (Q := Q) inputStack encodeInput data 0 =
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).initialConfiguration := by
  apply BankConfiguration.ext <;>
    simp [inputState, inputStore, stackState, bank, TapeBank.initialConfiguration, Function.update_eq_self]
  funext j position
  exact tape_nil position

theorem auxiliary_start (data : InputData I A) (different : inputStack ≠ auxiliaryStack) :
    auxiliaryState (O := O) (Q := Q) inputStack auxiliaryStack encodeInput encodeAuxiliary data 0 =
      {inputState (O := O) (Q := Q) inputStack encodeInput data data.input.length with state := .auxiliary} := by
  have empty : inputStore inputStack encodeInput data data.input.length auxiliaryStack = [] := by
    simp [inputStore, different.symm]
  have stores : auxiliaryStore inputStack auxiliaryStack encodeInput encodeAuxiliary data 0 =
      inputStore inputStack encodeInput data data.input.length := by
    simp [auxiliaryStore, ← empty, Function.update_eq_self]
  simp only [auxiliaryState, inputState, stores, stackState]

theorem input_handoff (data : InputData I A) (bits : BitString) (different : inputStack ≠ auxiliaryStack) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Steps data bits
      (inputState inputStack encodeInput data data.input.length) 1
      (auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data 0) := by
  rw [auxiliary_start inputStack auxiliaryStack encodeInput encodeAuxiliary data different]
  apply TapeBank.Steps.go (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary) data bits
    (inputState inputStack encodeInput data data.input.length) Phase.auxiliary
  · exact le_rfl
  · exact Nat.zero_le _
  · exact Nat.zero_le _
  · simp [bank, TapeBank.instruction, inputState, stackState]

theorem auxiliary_end (data : InputData I A) :
    {auxiliaryState (O := O) (Q := Q) inputStack auxiliaryStack encodeInput encodeAuxiliary data data.auxiliary.length
      with state := .body (.ready P.initial)} =
      externalize data (P.encoded ((loadedMemory inputStack auxiliaryStack encodeInput encodeAuxiliary data).at P.initial)) := rfl

theorem auxiliary_handoff (data : InputData I A) (bits : BitString) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Steps data bits
      (auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data data.auxiliary.length) 1
      (externalize data (P.encoded ((loadedMemory inputStack auxiliaryStack encodeInput encodeAuxiliary data).at P.initial))) := by
  rw [← auxiliary_end P inputStack auxiliaryStack encodeInput encodeAuxiliary data]
  apply TapeBank.Steps.go (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary) data bits
    (auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data data.auxiliary.length)
    (Phase.body (.ready P.initial))
  · exact le_rfl
  · exact le_rfl
  · exact Nat.zero_le _
  · simp [bank, TapeBank.instruction, auxiliaryState, stackState]

/-- Both words have been copied into genuine stacks after a linear number of
bank steps. Stack tops expose their reversed words for the controller's
ordinary verified transfer routine. -/
theorem load_prefix (data : InputData I A) (bits : BitString) (different : inputStack ≠ auxiliaryStack) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Steps data bits
      (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).initialConfiguration
      (2 * data.input.length + 1 + 2 * data.auxiliary.length + 1)
      (externalize data (P.encoded ((loadedMemory inputStack auxiliaryStack encodeInput encodeAuxiliary data).at P.initial))) := by
  let B := bank P inputStack auxiliaryStack encodeInput encodeAuxiliary
  have first := input_prefix P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits data.input.length le_rfl
  rw [input_initial P inputStack auxiliaryStack encodeInput encodeAuxiliary data] at first
  have enter := input_handoff P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits different
  have second := auxiliary_prefix P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits data.auxiliary.length le_rfl
  have finish := auxiliary_handoff P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits
  exact ((first.trans B enter).trans B second).trans B finish

end ComplexityOfGenerators.Simulation.WordStack.InputBank
