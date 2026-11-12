import ComplexityOfGenerators.Simulation.WordStack.InputBank.StackState

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank

open TransducerBank

set_option backward.isDefEq.respectTransparency false

variable {I A Q S O : Type} {k : ℕ} (P : Program Q S O k)
    (inputStack auxiliaryStack : Fin k) (encodeInput : I → S) (encodeAuxiliary : A → S)

def inputStore (data : InputData I A) (read : ℕ) : Fin k → List S :=
  Function.update (fun _ => []) inputStack ((data.input.take read).reverse.map encodeInput)

def auxiliaryStore (data : InputData I A) (read : ℕ) : Fin k → List S :=
  Function.update (inputStore inputStack encodeInput data data.input.length) auxiliaryStack
    ((data.auxiliary.take read).reverse.map encodeAuxiliary)

def inputState (data : InputData I A) (read : ℕ) : BankConfiguration O (Phase I A Q S k) (Option S) k :=
  stackState .input (inputStore inputStack encodeInput data read) read 0

def auxiliaryState (data : InputData I A) (read : ℕ) : BankConfiguration O (Phase I A Q S k) (Option S) k :=
  stackState .auxiliary (auxiliaryStore inputStack auxiliaryStack encodeInput encodeAuxiliary data read)
    data.input.length read

theorem inputStore_succ (data : InputData I A) (read : ℕ) (inside : read < data.input.length) :
    inputStore inputStack encodeInput data (read + 1) =
      Function.update (inputStore inputStack encodeInput data read) inputStack
        (encodeInput data.input[read] :: inputStore inputStack encodeInput data read inputStack) := by
  have take : (data.input.take (read + 1)).reverse.map encodeInput =
      encodeInput data.input[read] :: (data.input.take read).reverse.map encodeInput := by
    rw [List.take_add_one, List.getElem?_eq_getElem inside]
    change ((data.input.take read ++ [data.input[read]]).reverse.map encodeInput) = _
    rw [List.reverse_append, List.map_append]
    rfl
  simp [inputStore, take, Function.update_idem]

theorem auxiliaryStore_succ (data : InputData I A) (read : ℕ) (inside : read < data.auxiliary.length) :
    auxiliaryStore inputStack auxiliaryStack encodeInput encodeAuxiliary data (read + 1) =
      Function.update (auxiliaryStore inputStack auxiliaryStack encodeInput encodeAuxiliary data read) auxiliaryStack
        (encodeAuxiliary data.auxiliary[read] :: auxiliaryStore inputStack auxiliaryStack encodeInput encodeAuxiliary data read auxiliaryStack) := by
  have take : (data.auxiliary.take (read + 1)).reverse.map encodeAuxiliary =
      encodeAuxiliary data.auxiliary[read] :: (data.auxiliary.take read).reverse.map encodeAuxiliary := by
    rw [List.take_add_one, List.getElem?_eq_getElem inside]
    change ((data.auxiliary.take read ++ [data.auxiliary[read]]).reverse.map encodeAuxiliary) = _
    rw [List.reverse_append, List.map_append]
    rfl
  simp [auxiliaryStore, take, Function.update_idem]

theorem input_step (data : InputData I A) (bits : BitString) (read : ℕ) (inside : read < data.input.length) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Steps data bits
      (inputState inputStack encodeInput data read) 2 (inputState inputStack encodeInput data (read + 1)) := by
  let B := bank P inputStack auxiliaryStack encodeInput encodeAuxiliary
  let source := inputState (O := O) (Q := Q) inputStack encodeInput data read
  let letter := data.input[read]
  let cell := source.tape inputStack (source.head inputStack)
  let pending := B.advance data source (.inputWrite letter) cell .right .right .stay .stay none
  have first : B.instruction data source = .step (.inputWrite letter) cell .right .right .stay .stay none := by
    simp [B, bank, TapeBank.instruction, source, inputState, stackState,
      List.getElem?_eq_getElem inside, letter, cell]
  have second : B.instruction data pending = .step .input (some (encodeInput letter)) .stay .stay .stay .stay none := by
    simp [B, bank, pending, TapeBank.instruction, TapeBank.advance]
  have final : B.advance data pending .input (some (encodeInput letter)) .stay .stay .stay .stay none =
      inputState inputStack encodeInput data (read + 1) := by
    have pushed := push_stackState B data (inputStore inputStack encodeInput data read) inputStack
      .input (.inputWrite letter) .input (encodeInput letter) .right .stay read 0
      (by omega) (Nat.zero_le _) rfl rfl
    simpa [pending, source, inputState, cell, stackState, B, inputStore_succ inputStack encodeInput data read inside,
      Move.onInput, Nat.min_eq_left (show read + 1 ≤ data.input.length by omega)] using pushed
  have path := TapeBank.Steps.step source (.inputWrite letter) cell .right .right .stay .stay none
    1 _ first (TapeBank.Steps.single B data bits pending _ _ _ _ _ _ _ second)
  simpa only [final] using path

theorem auxiliary_step (data : InputData I A) (bits : BitString) (read : ℕ) (inside : read < data.auxiliary.length) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Steps data bits
      (auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data read) 2
      (auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data (read + 1)) := by
  let B := bank P inputStack auxiliaryStack encodeInput encodeAuxiliary
  let source := auxiliaryState (O := O) (Q := Q) inputStack auxiliaryStack encodeInput encodeAuxiliary data read
  let letter := data.auxiliary[read]
  let cell := source.tape auxiliaryStack (source.head auxiliaryStack)
  let pending := B.advance data source (.auxiliaryWrite letter) cell .right .stay .right .stay none
  have first : B.instruction data source = .step (.auxiliaryWrite letter) cell .right .stay .right .stay none := by
    simp [B, bank, TapeBank.instruction, source, auxiliaryState, stackState,
      List.getElem?_eq_getElem inside, letter, cell]
  have second : B.instruction data pending = .step .auxiliary (some (encodeAuxiliary letter)) .stay .stay .stay .stay none := by
    simp [B, bank, pending, TapeBank.instruction, TapeBank.advance]
  have final : B.advance data pending .auxiliary (some (encodeAuxiliary letter)) .stay .stay .stay .stay none =
      auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data (read + 1) := by
    have pushed := push_stackState B data (auxiliaryStore inputStack auxiliaryStack encodeInput encodeAuxiliary data read)
      auxiliaryStack .auxiliary (.auxiliaryWrite letter) .auxiliary (encodeAuxiliary letter)
      .stay .right data.input.length read le_rfl (by omega) rfl rfl
    simpa [pending, source, auxiliaryState, cell, stackState, B,
      auxiliaryStore_succ inputStack auxiliaryStack encodeInput encodeAuxiliary data read inside,
      Move.onInput, Nat.min_eq_left (show read + 1 ≤ data.auxiliary.length by omega)] using pushed
  have path := TapeBank.Steps.step source (.auxiliaryWrite letter) cell .right .stay .right .stay none
    1 _ first (TapeBank.Steps.single B data bits pending _ _ _ _ _ _ _ second)
  simpa only [final] using path

theorem input_prefix (data : InputData I A) (bits : BitString) (read : ℕ) (bound : read ≤ data.input.length) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Steps data bits
      (inputState inputStack encodeInput data 0) (2 * read) (inputState inputStack encodeInput data read) := by
  induction read with
  | zero => exact .refl _
  | succ read ih =>
    have earlier := ih (by omega)
    have next := input_step P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits read (by omega)
    simpa [Nat.mul_add] using earlier.trans (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary) next

theorem auxiliary_prefix (data : InputData I A) (bits : BitString) (read : ℕ) (bound : read ≤ data.auxiliary.length) :
    (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary).Steps data bits
      (auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data 0) (2 * read)
      (auxiliaryState inputStack auxiliaryStack encodeInput encodeAuxiliary data read) := by
  induction read with
  | zero => exact .refl _
  | succ read ih =>
    have earlier := ih (by omega)
    have next := auxiliary_step P inputStack auxiliaryStack encodeInput encodeAuxiliary data bits read (by omega)
    simpa [Nat.mul_add] using earlier.trans (bank P inputStack auxiliaryStack encodeInput encodeAuxiliary) next

end ComplexityOfGenerators.Simulation.WordStack.InputBank
