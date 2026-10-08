import ComplexityOfGenerators.Simulation.CollisionParserData

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

theorem collision_advance_word (word : BitString) (c : BankConfiguration
    (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7)
    (next : CollisionPhase M.states M.symbols) (j : Fin 7) (xs : BitString) (b : Bool) (input : Move)
    (select : (collisionBank M).select c.state = j)
    (head : c.head j = (xs.length : ℤ)) (tape : c.tape j = collisionWord M xs) :
    (collisionBank M).advance word c next (collisionBit M b) .right input =
      {c with
        state := next
        inputHead := input.onInput word.length c.inputHead
        head := Function.update c.head j (xs.length + 1)
        tape := Function.update c.tape j (collisionWord M (xs ++ [b]))} := by
  simp only [TapeBank.advance, select, head, tape, Move.onInt, collisionWord_append]

theorem collisionX_read_header (word x : BitString) (rest : BitString)
    (encoding : word = collisionBits x ++ false :: rest) :
    (collisionBank M).Steps word (collisionXConfiguration M x) 1
      {collisionXConfiguration M x with state := .xBit (!x.isEmpty), inputHead := 2 * x.length + 1} := by
  let c := collisionXConfiguration M x
  have read : word[2 * x.length]? = some false := by
    rw [encoding, ← collisionBits_length x]
    simp
  have bound : 2 * x.length + 1 ≤ word.length := by simp [encoding]
  have action : (collisionBank M).instruction word c =
      .step (.xBit (!x.isEmpty)) (c.tape 0 (c.head 0)) .stay .right := by
    simp [TapeBank.instruction, collisionBank, c, collisionXConfiguration,
      collisionSelect, collisionTransition, read]
  have run := TapeBank.Steps.single (collisionBank M) word c _ _ .stay .right action
  have advance := TapeBank.advance_read_input (collisionBank M) word c (.xBit (!x.isEmpty)) .stay .right
  simp only [show (collisionBank M).select c.state = 0 by rfl] at advance
  rw [advance] at run
  simp only [Move.onInt, Function.update_eq_self] at run
  simpa [c, collisionXConfiguration, Move.onInt, Move.onInput,
    Nat.min_eq_left bound, Function.update_eq_self] using run

/-- Loading a binary data symbol also extends the unary index after the first
symbol. This establishes exactly the `n = input.length - 1` convention. -/
theorem collisionX_load_bit (word x : BitString) (b : Bool) (rest : BitString)
    (encoding : word = collisionBits x ++ false :: b :: rest) :
    ∃ t, t ≤ 3 ∧ (collisionBank M).Steps word (collisionXConfiguration M x) t
      (collisionXConfiguration M (x ++ [b])) := by
  let B := collisionBank M
  let c := collisionXConfiguration M x
  let d := {c with
    state := CollisionPhase.xBit (states := M.states) (symbols := M.symbols) (!x.isEmpty)
    inputHead := 2 * x.length + 1}
  have first : B.Steps word c 1 d := collisionX_read_header M word x (b :: rest) encoding
  have read : word[2 * x.length + 1]? = some b := by
    rw [encoding, ← collisionBits_length x]
    simp [List.getElem?_append_right]
  have bound : 2 * x.length + 2 ≤ word.length := by simp [encoding]
  let next : CollisionPhase M.states M.symbols := if !x.isEmpty then .indexBit else .xHeader true
  have action : B.instruction word d = .step next (collisionBit M b) .right .right := by
    simp [B, TapeBank.instruction, collisionBank, d, collisionSelect, collisionTransition, read, next]
  let e := B.advance word d next (collisionBit M b) .right .right
  have second : B.Steps word d 1 e := TapeBank.Steps.single B word d _ _ .right .right action
  have advanced : e =
      {d with
        state := next
        inputHead := 2 * x.length + 2
        head := Function.update d.head 0 (x.length + 1)
        tape := Function.update d.tape 0 (collisionWord M (x ++ [b]))} := by
    have update := collision_advance_word M word d next 0 x b .right rfl
      (by simp [d, c, collisionXConfiguration])
      (by simp [d, c, collisionXConfiguration, collisionLoadedTapes])
    simpa [e, B, Move.onInput, d, Nat.min_eq_left bound, Nat.add_assoc] using update
  cases x with
  | nil =>
      refine ⟨2, by omega, ?_⟩
      have equal : e = collisionXConfiguration M [b] := by
        rw [advanced]
        apply BankConfiguration.ext
        · rfl
        · rfl
        · funext j
          simp [d, c, next, collisionXConfiguration, Function.update_apply,
            TapeBank.initialConfiguration, collisionBank]
          omega
        · funext j i
          simp [d, c, collisionXConfiguration, collisionLoadedTapes, Function.update_apply,
            TapeBank.initialConfiguration, collisionBank]
          split_ifs <;> simp_all
      simpa only [List.nil_append, equal] using first.trans B second
  | cons a xs =>
      have indexLength : (a :: xs).length - 1 = xs.length := by simp
      have current : e.tape 2 = collisionWord M (List.replicate xs.length true) := by
        simp [advanced, d, c, collisionXConfiguration, collisionLoadedTapes]
      have head : e.head 2 = (xs.length : ℤ) := by simp [advanced, d, c, collisionXConfiguration]
      have state : e.state = .indexBit := by simp [advanced, next]
      have thirdAction : B.instruction word e = .step (.xHeader true) (collisionBit M true) .right .stay := by
        simp [B, TapeBank.instruction, collisionBank, state, collisionTransition]
      have third := TapeBank.Steps.single B word e (.xHeader true) _ .right .stay thirdAction
      have update := collision_advance_word M word e (.xHeader true) 2
        (List.replicate xs.length true) true .stay (by simp [B, collisionBank, state, collisionSelect])
        (by simpa using head) current
      have equal : B.advance word e (.xHeader true) (collisionBit M true) .right .stay =
          collisionXConfiguration M ((a :: xs) ++ [b]) := by
        rw [update, advanced]
        apply BankConfiguration.ext
        · rfl
        · change min (2 * (a :: xs).length + 2) word.length = 2 * ((a :: xs) ++ [b]).length
          rw [Nat.min_eq_left bound]
          simp; omega
        · funext j
          simp [d, c, collisionXConfiguration, Function.update_apply]
          split_ifs <;> simp_all
        · funext j i
          simp [d, c, collisionXConfiguration, collisionLoadedTapes, Function.update_apply,
            ← List.replicate_add]
          split_ifs <;> simp_all
          rw [List.replicate_succ']
      rw [equal] at third
      exact ⟨3, by omega, (first.trans B second).trans B third⟩

end
end ComplexityOfGenerators.Simulation
