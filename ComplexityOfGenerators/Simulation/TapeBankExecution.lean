import ComplexityOfGenerators.Simulation.TapeBankTime

/-! Composable finite execution paths for tape-bank programs. -/

namespace ComplexityOfGenerators.Simulation.TapeBank

variable {Q S : Type} {k : ℕ} (B : TapeBank Q S k)

theorem advance_read_input (word : BitString) (c : BankConfiguration Q S k)
    (next : Q) (work input : Move) :
    B.advance word c next (c.tape (B.select c.state) (c.head (B.select c.state))) work input =
      {c with
        state := next
        inputHead := input.onInput word.length c.inputHead
        head := Function.update c.head (B.select c.state) (work.onInt (c.head (B.select c.state)))} := by
  simp [advance, Function.update_eq_self]

theorem advance_read (word : BitString) (c : BankConfiguration Q S k)
    (next : Q) (work : Move) (bounded : c.inputHead ≤ word.length) :
    B.advance word c next (c.tape (B.select c.state) (c.head (B.select c.state))) work .stay =
      {c with
        state := next
        head := Function.update c.head (B.select c.state) (work.onInt (c.head (B.select c.state)))} := by
  simp [advance, Function.update_eq_self, Move.onInput, Nat.min_eq_left bounded]

theorem advance_stay (word : BitString) (c : BankConfiguration Q S k)
    (next : Q) (bounded : c.inputHead ≤ word.length) :
    B.advance word c next (c.tape (B.select c.state) (c.head (B.select c.state))) .stay .stay =
      {c with state := next} := by
  rw [advance_read B word c next .stay bounded]
  simp [Move.onInt, Function.update_eq_self]

inductive Steps (word : BitString) : BankConfiguration Q S k → ℕ → BankConfiguration Q S k → Prop
  | refl (c) : Steps word c 0 c
  | step (c) (next write work input) (t d)
      (table : B.instruction word c = .step next write work input)
      (rest : Steps word (B.advance word c next write work input) t d) :
      Steps word c (t + 1) d

theorem Steps.single (word : BitString) (c : BankConfiguration Q S k)
    (next write work input) (table : B.instruction word c = .step next write work input) :
    B.Steps word c 1 (B.advance word c next write work input) :=
  .step c next write work input 0 _ table (.refl _)

theorem Steps.trans {word : BitString} {a b c : BankConfiguration Q S k} {s t : ℕ}
    (left : B.Steps word a s b) (right : B.Steps word b t c) :
    B.Steps word a (s + t) c := by
  induction left with
  | refl => simpa using right
  | step a next write work input s b table rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.step a next write work input (s + t) c table (ih right)

theorem Steps.executes {word : BitString} {a b : BankConfiguration Q S k} {s t : ℕ} {result : Bool}
    (path : B.Steps word a s b) (halt : B.Executes word b t result) :
    B.Executes word a (s + t) result := by
  induction path with
  | refl => simpa using halt
  | step a next write work input s b table rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Executes.step a next write work input (s + t) result table (ih halt)

end ComplexityOfGenerators.Simulation.TapeBank
