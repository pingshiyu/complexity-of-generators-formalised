import ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped.Scan

namespace ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped

open TransducerBank
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k) (counter : Fin k)

theorem rewind_step (data : InputData I A) (bits : BitString) (side : Bool) (position : ℕ)
    (length : position + 1 ≤ wordLength data side) (index : position + 1 ≤ data.index) :
    (bank B counter).Steps data bits (state B counter (.rewind side) side (position + 1)) 1
      (state B counter (.rewind side) side position) := by
  let source := state (O := O) B counter (.rewind side) side (position + 1)
  have instruction : (bank B counter).instruction data source =
      .step (.rewind side) B.blank .left (if side then .stay else .left)
        (if side then .left else .stay) .left none := by
    simp [source, state, TapeBank.instruction, bank] <;> omega
  have one := TapeBank.Steps.single (bank B counter) data bits source _ _ _ _ _ _ _ instruction
  convert one using 1
  apply BankConfiguration.ext <;>
    simp [source, state, TapeBank.advance, bank, Move.onInput, Move.onInt,
      Function.update_idem, Function.update_eq_self] <;>
    cases side <;> simp_all [wordLength, Nat.min_eq_left] <;> omega

theorem rewind_prefix (data : InputData I A) (bits : BitString) (side : Bool) (count : ℕ)
    (length : count ≤ wordLength data side) (index : count ≤ data.index) :
    (bank B counter).Steps data bits (state B counter (.rewind side) side count) count
      (state B counter (.rewind side) side 0) := by
  induction count with
  | zero => exact .refl _
  | succ count ih =>
      simpa [Nat.add_comm] using
        (rewind_step B counter data bits side count length index).trans _ (ih (by omega) (by omega))

theorem rewind_finish (data : InputData I A) (bits : BitString) (side : Bool) :
    (bank B counter).Steps data bits (state B counter (.rewind side) side 0) 1
      (state B counter (if side then .body B.initial else .scan true) side 0) := by
  apply TapeBank.Steps.go (bank B counter) data bits _ (if side then .body B.initial else .scan true)
  · cases side <;> simp [state]
  · cases side <;> simp [state]
  · exact Nat.zero_le _
  · simp [TapeBank.instruction, bank, state]

theorem check_short (data : InputData I A) (bits : BitString) (side : Bool)
    (short : wordLength data side ≤ data.index) :
    (bank B counter).Steps data bits (state B counter (.scan side) side 0)
      (2 * wordLength data side + 2)
      (state B counter (if side then .body B.initial else .scan true) side 0) := by
  have scan := scan_prefix B counter data bits side (wordLength data side) le_rfl short
  have turn := scan_finish B counter data bits side short
  have rewind := rewind_prefix B counter data bits side (wordLength data side) le_rfl short
  have finish := rewind_finish B counter data bits side
  have path := ((scan.trans _ turn).trans _ rewind).trans _ finish
  convert path using 1 <;> omega

theorem checked_prefix (data : InputData I A) (bits : BitString)
    (input : data.input.length ≤ data.index) (auxiliary : data.auxiliary.length ≤ data.index) :
    (bank B counter).Steps data bits (bank B counter).initialConfiguration
      (2 * data.input.length + 2 * data.auxiliary.length + 4)
      (B.initialConfiguration.mapState Phase.body) := by
  have first := check_short B counter data bits false input
  have second := check_short B counter data bits true auxiliary
  have middle : state (O := O) B counter (.scan true) false 0 =
      state B counter (.scan true) true 0 := by simp [state]
  have last : state (O := O) B counter (.body B.initial) true 0 =
      B.initialConfiguration.mapState Phase.body := by
    apply BankConfiguration.ext <;> simp [state, TapeBank.initialConfiguration, BankConfiguration.mapState]
  have path := first.trans _ second
  simp only [wordLength, Bool.false_eq_true, ite_false, ite_true, initial_state, middle, last] at path
  convert path using 1 <;> omega

end ComplexityOfGenerators.Simulation.WordStack.InputBank.Capped
