import ComplexityOfGenerators.Simulation.CollisionParserSteps

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

theorem collisionY_read_header (word x y rest : BitString)
    (encoding : word = collisionBits x ++ true :: false :: (collisionBits y ++ false :: rest)) :
    (collisionBank M).Steps word (collisionYConfiguration M x y) 1
      {collisionYConfiguration M x y with
        state := .yBit (decide (x.take y.length ≠ y))
        inputHead := 2 * x.length + 2 + 2 * y.length + 1} := by
  let c := collisionYConfiguration M x y
  have read : word[2 * x.length + 2 + 2 * y.length]? = some false := by
    have enc : word = (collisionBits x ++ [true, false] ++ collisionBits y) ++ false :: rest := by
      simpa [List.append_assoc] using encoding
    have len : (collisionBits x ++ [true, false] ++ collisionBits y).length =
        2 * x.length + 2 + 2 * y.length := by simp; omega
    rw [enc, ← len]
    simp only [List.getElem?_append_right (by omega :
      (collisionBits x ++ [true, false] ++ collisionBits y).length ≤
        (collisionBits x ++ [true, false] ++ collisionBits y).length), Nat.sub_self, List.getElem?_cons_zero]
  have bound : 2 * x.length + 2 + 2 * y.length + 1 ≤ word.length := by simp [encoding]; omega
  have action : (collisionBank M).instruction word c =
      .step (.yBit (decide (x.take y.length ≠ y))) (c.tape 0 (c.head 0)) .stay .right := by
    simp [TapeBank.instruction, collisionBank, c, collisionYConfiguration,
      collisionSelect, collisionTransition, read]
  have run := TapeBank.Steps.single (collisionBank M) word c _ _ .stay .right action
  have advance := TapeBank.advance_read_input (collisionBank M) word c
    (.yBit (decide (x.take y.length ≠ y))) .stay .right
  simp only [show (collisionBank M).select c.state = 0 by rfl] at advance
  rw [advance] at run
  simp only [Move.onInt, Function.update_eq_self] at run
  simpa [c, collisionYConfiguration, Move.onInput, Nat.min_eq_left bound] using run

theorem collisionY_difference (x y : BitString) (a b : Bool) (read : x[y.length]? = some a) :
    decide (x.take (y ++ [b]).length ≠ y ++ [b]) =
      (decide (x.take y.length ≠ y) || decide (a ≠ b)) := by
  have eq : x.take y.length ++ [a] = y ++ [b] ↔ x.take y.length = y ∧ a = b := by
    constructor
    · intro h
      obtain ⟨h₁, h₂⟩ := List.append_inj' h (by simp)
      exact ⟨h₁, by simpa using h₂⟩
    · rintro ⟨h₁, h₂⟩
      rw [h₁, h₂]
  simp only [List.length_append, List.length_singleton, List.take_succ, read, Option.toList_some,
    ne_eq, eq, not_and_or]
  by_cases h : x.take y.length = y <;> by_cases h' : a = b <;> simp_all

theorem collisionY_load_bit (word x y rest : BitString) (a b : Bool)
    (encoding : word = collisionBits x ++ true :: false :: (collisionBits y ++ false :: b :: rest))
    (current : x[y.length]? = some a) :
    (collisionBank M).Steps word (collisionYConfiguration M x y) 3
      (collisionYConfiguration M x (y ++ [b])) := by
  let B := collisionBank M
  let c := collisionYConfiguration M x y
  let different := decide (x.take y.length ≠ y) || decide (a ≠ b)
  let d := {c with
    state := CollisionPhase.yBit (states := M.states) (symbols := M.symbols) (decide (x.take y.length ≠ y))
    inputHead := 2 * x.length + 2 + 2 * y.length + 1}
  let e : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 := {d with
    state := CollisionPhase.storeY b different
    head := Function.update d.head 0 (y.length + 1)}
  have first : B.Steps word c 1 d := collisionY_read_header M word x y (b :: rest) encoding
  have read : word[2 * x.length + 2 + 2 * y.length + 1]? = some b := by
    have enc : word = (collisionBits x ++ [true, false] ++ collisionBits y) ++ false :: b :: rest := by
      simpa [List.append_assoc] using encoding
    have len : (collisionBits x ++ [true, false] ++ collisionBits y).length =
        2 * x.length + 2 + 2 * y.length := by simp; omega
    rw [enc, ← len]
    rw [List.getElem?_append_right (by omega)]
    simp
  have bound : 2 * x.length + 2 + 2 * y.length + 2 ≤ word.length := by simp [encoding]; omega
  have action : B.instruction word d =
      .step (.storeY b different) (d.tape 0 (d.head 0)) .right .stay := by
    simp [B, TapeBank.instruction, collisionBank, d, c, collisionYConfiguration,
      collisionLoadedTapes, collisionSelect, collisionTransition, read, current, different]
  have second := TapeBank.Steps.single B word d _ _ .right .stay action
  have advance := TapeBank.advance_read B word d (.storeY b different) .right (by dsimp [d]; omega)
  simp only [show B.select d.state = 0 by rfl] at advance
  rw [advance] at second
  have second' : B.Steps word d 1 e := by simpa [e, d, c, collisionYConfiguration, Move.onInt] using second
  have action' : B.instruction word e = .step (.yHeader different) (collisionBit M b) .right .right := by
    simp [B, TapeBank.instruction, collisionBank, e, collisionTransition]
  have third := TapeBank.Steps.single B word e _ _ .right .right action'
  have update := collision_advance_word M word e (.yHeader different) 1 y b .right rfl
    (by simp [e, d, c, collisionYConfiguration])
    (by simp [e, d, c, collisionYConfiguration, collisionLoadedTapes])
  have equal : B.advance word e (.yHeader different) (collisionBit M b) .right .right =
      collisionYConfiguration M x (y ++ [b]) := by
    rw [update]
    apply BankConfiguration.ext
    · exact congrArg CollisionPhase.yHeader (collisionY_difference x y a b current).symm
    · change min (2 * x.length + 2 + 2 * y.length + 1 + 1) word.length =
        2 * x.length + 2 + 2 * (y ++ [b]).length
      rw [Nat.min_eq_left (by omega)]
      simp; omega
    · funext j
      simp [e, d, c, collisionYConfiguration, Function.update_apply]
      split_ifs <;> simp_all
    · funext j i
      simp [e, d, c, collisionYConfiguration, collisionLoadedTapes, Function.update_apply]
      split_ifs <;> simp_all
  rw [equal] at third
  exact (first.trans B second').trans B third

end
end ComplexityOfGenerators.Simulation
