import ComplexityOfGenerators.Simulation.CollisionParserSteps

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

theorem collisionX_read_separator (word x rest : BitString)
    (encoding : word = collisionBits x ++ true :: rest) :
    (collisionBank M).Steps word (collisionXConfiguration M x) 1
      {collisionXConfiguration M x with state := .separator (!x.isEmpty), inputHead := 2 * x.length + 1} := by
  let c := collisionXConfiguration M x
  have read : word[2 * x.length]? = some true := by
    rw [encoding, ← collisionBits_length x]
    simp
  have bound : 2 * x.length + 1 ≤ word.length := by simp [encoding]
  have action : (collisionBank M).instruction word c =
      .step (.separator (!x.isEmpty)) (c.tape 0 (c.head 0)) .stay .right := by
    simp [TapeBank.instruction, collisionBank, c, collisionXConfiguration,
      collisionSelect, collisionTransition, read]
  have run := TapeBank.Steps.single (collisionBank M) word c _ _ .stay .right action
  have advance := TapeBank.advance_read_input (collisionBank M) word c (.separator (!x.isEmpty)) .stay .right
  simp only [show (collisionBank M).select c.state = 0 by rfl] at advance
  rw [advance] at run
  simp only [Move.onInt, Function.update_eq_self] at run
  simpa [c, collisionXConfiguration, Move.onInput, Nat.min_eq_left bound] using run

theorem collisionX_separator (word x rest : BitString) (positive : x ≠ [])
    (encoding : word = collisionBits x ++ true :: false :: rest) :
    (collisionBank M).Steps word (collisionXConfiguration M x) (x.length + 3)
      (collisionYConfiguration M x []) := by
  let B := collisionBank M
  let c := collisionXConfiguration M x
  let d := {c with
    state := CollisionPhase.separator (states := M.states) (symbols := M.symbols) (!x.isEmpty)
    inputHead := 2 * x.length + 1}
  let e := {c with
    state := CollisionPhase.rewindX (states := M.states) (symbols := M.symbols)
    inputHead := 2 * x.length + 2}
  have seen : x.isEmpty = false := by cases x <;> simp_all
  have first : B.Steps word c 1 d := collisionX_read_separator M word x (false :: rest) encoding
  have read : word[2 * x.length + 1]? = some false := by
    rw [encoding, ← collisionBits_length x]
    simp
  have bound : 2 * x.length + 2 ≤ word.length := by simp [encoding]
  have action : B.instruction word d = .step .rewindX (d.tape 0 (d.head 0)) .stay .right := by
    simp [B, TapeBank.instruction, collisionBank, d, collisionSelect, collisionTransition, read, seen]
  have second := TapeBank.Steps.single B word d _ _ .stay .right action
  have advance := TapeBank.advance_read_input B word d .rewindX .stay .right
  simp only [show B.select d.state = 0 by rfl] at advance
  rw [advance] at second
  simp only [Move.onInt, Function.update_eq_self] at second
  have second' : B.Steps word d 1 e := by simpa [d, e, Move.onInput, Nat.min_eq_left bound, Nat.add_assoc] using second
  have rewind := TapeBank.rewind B word .rewindX (.yHeader false) 0 rfl
    (fun _ _ _ => rfl) x.length e rfl (by simp [e, c, collisionXConfiguration]) bound
  have equal : {e with state := CollisionPhase.yHeader false, head := Function.update e.head 0 0} =
      collisionYConfiguration M x [] := by
    apply BankConfiguration.ext
    · simp [collisionYConfiguration]
    · rfl
    · funext j
      simp [e, c, collisionXConfiguration, collisionYConfiguration, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  rw [equal] at rewind
  simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using (first.trans B second').trans B rewind

end
end ComplexityOfGenerators.Simulation
