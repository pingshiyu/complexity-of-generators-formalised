import ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped.Basic

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

open TransducerBank
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k) (counter : Fin k)

private theorem blank_update (value : S) (j : Fin k) (position : ℤ) :
    Function.update (fun _ : Fin k => fun _ : ℤ => value) j
      (Function.update (fun _ : ℤ => value) position value) = fun _ _ => value := by
  simp [Function.update_eq_self]

theorem scan_step (data : InputData I A) (bits : BitString) (side : Bool) (position : ℕ)
    (inside : position < wordLength data side) (index : position < data.index) :
    (bank B counter).Steps data bits (state B counter (.scan side) side position) 1
      (state B counter (.scan side) side (position + 1)) := by
  let source := state (O := O) B counter (.scan side) side position
  have instruction : (bank B counter).instruction data source =
      .step (.scan side) B.blank .right (if side then .stay else .right)
        (if side then .right else .stay) .right none := by
    cases side <;>
      simp [source, state, TapeBank.instruction, bank, wordLength] at inside ⊢ <;>
      simp [List.getElem?_eq_getElem inside, index] <;> assumption
  have one := TapeBank.Steps.single (bank B counter) data bits source _ _ _ _ _ _ _ instruction
  convert one using 1
  apply BankConfiguration.ext <;>
    simp [source, state, TapeBank.advance, bank, Move.onInput, Move.onInt,
      Nat.min_eq_left (show position + 1 ≤ data.index by omega), Function.update_idem,
      blank_update] <;>
    cases side <;> simp_all [wordLength, Nat.min_eq_left] <;> omega

theorem scan_prefix (data : InputData I A) (bits : BitString) (side : Bool) (count : ℕ)
    (length : count ≤ wordLength data side) (index : count ≤ data.index) :
    (bank B counter).Steps data bits (state B counter (.scan side) side 0) count
      (state B counter (.scan side) side count) := by
  induction count with
  | zero => exact .refl _
  | succ count ih =>
      exact (ih (by omega) (by omega)).trans _
        (scan_step B counter data bits side count (by omega) (by omega))

theorem scan_finish (data : InputData I A) (bits : BitString) (side : Bool)
    (index : wordLength data side ≤ data.index) :
    (bank B counter).Steps data bits
      (state B counter (.scan side) side (wordLength data side)) 1
      (state B counter (.rewind side) side (wordLength data side)) := by
  apply TapeBank.Steps.go (bank B counter) data bits _ (.rewind side)
  · cases side <;> simp [state, wordLength]
  · cases side <;> simp [state, wordLength]
  · exact index
  · cases side <;> simp [TapeBank.instruction, bank, state, wordLength]

theorem scan_oversize (data : InputData I A) (bits : BitString) (side : Bool)
    (oversized : data.index < wordLength data side) :
    (bank B counter).Steps data bits
      (state B counter (.scan side) side data.index) 1
      (state B counter .drain side data.index) := by
  apply TapeBank.Steps.go (bank B counter) data bits _ .drain
  · cases side <;> simp_all [state, wordLength] <;> omega
  · cases side <;> simp_all [state, wordLength] <;> omega
  · exact le_rfl
  · cases side <;>
      simp [state, wordLength] at oversized ⊢ <;>
      simp [TapeBank.instruction, bank, state, List.getElem?_eq_getElem oversized]

end ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped
