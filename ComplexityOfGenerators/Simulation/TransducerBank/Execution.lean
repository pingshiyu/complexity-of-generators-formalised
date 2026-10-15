import ComplexityOfGenerators.Simulation.TransducerBank.Time

/-! Composable finite execution paths for tape-bank programs. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem advance_read (data : InputData I A) (c : BankConfiguration O Q S k)
    (next : Q) (work : Move)
    (input : c.inputHead ≤ data.input.length) (auxiliary : c.auxiliaryHead ≤ data.auxiliary.length)
    (index : c.indexHead ≤ data.index) :
    B.advance data c next (c.tape (B.select c.state) (c.head (B.select c.state))) work .stay .stay .stay none =
      {c with state := next, head := Function.update c.head (B.select c.state) (work.onInt (c.head (B.select c.state)))} := by
  simp [advance, Function.update_eq_self, Move.onInput, Nat.min_eq_left input,
    Nat.min_eq_left auxiliary, Nat.min_eq_left index]

theorem advance_stay (data : InputData I A) (c : BankConfiguration O Q S k) (next : Q)
    (input : c.inputHead ≤ data.input.length) (auxiliary : c.auxiliaryHead ≤ data.auxiliary.length)
    (index : c.indexHead ≤ data.index) :
    B.advance data c next (c.tape (B.select c.state) (c.head (B.select c.state))) .stay .stay .stay .stay none =
      {c with state := next} := by
  rw [advance_read B data c next .stay input auxiliary index]
  simp [Move.onInt, Function.update_eq_self]

inductive Steps (data : InputData I A) (bits : BitString) : BankConfiguration O Q S k → ℕ → BankConfiguration O Q S k → Prop
  | refl (c) : Steps data bits c 0 c
  | random (c) (no yes : Q) (bit : Bool) (t d)
      (table : B.instruction data c = .readRandom no yes) (lookup : bits[c.randomHead]? = some bit)
      (rest : Steps data bits (choose c (if bit then yes else no)) t d) :
      Steps data bits c (t + 1) d
  | step (c) (next write work input auxiliary index emit) (t d)
      (table : B.instruction data c = .step next write work input auxiliary index emit)
      (rest : Steps data bits (B.advance data c next write work input auxiliary index emit) t d) :
      Steps data bits c (t + 1) d

theorem Steps.single (data : InputData I A) (bits : BitString) (c : BankConfiguration O Q S k)
    (next write work input auxiliary index emit) (table : B.instruction data c = .step next write work input auxiliary index emit) :
    B.Steps data bits c 1 (B.advance data c next write work input auxiliary index emit) :=
  .step c next write work input auxiliary index emit 0 _ table (.refl _)

theorem Steps.go (data : InputData I A) (bits : BitString) (c : BankConfiguration O Q S k) (next : Q)
    (input : c.inputHead ≤ data.input.length) (auxiliary : c.auxiliaryHead ≤ data.auxiliary.length)
    (index : c.indexHead ≤ data.index)
    (table : B.instruction data c = .step next
      (c.tape (B.select c.state) (c.head (B.select c.state))) .stay .stay .stay .stay none) :
    B.Steps data bits c 1 {c with state := next} := by
  have step := Steps.single B data bits c _ _ _ _ _ _ _ table
  simpa only [advance_stay B data c next input auxiliary index] using step

/-- A read-only instruction moves one virtual head and changes control. -/
theorem Steps.read (data : InputData I A) (bits : BitString) (c : BankConfiguration O Q S k)
    (next : Q) (work : Move) (j : Fin k) (selected : B.select c.state = j)
    (input : c.inputHead ≤ data.input.length) (auxiliary : c.auxiliaryHead ≤ data.auxiliary.length)
    (index : c.indexHead ≤ data.index)
    (table : B.instruction data c = .step next (c.tape j (c.head j)) work .stay .stay .stay none) :
    B.Steps data bits c 1
      {c with state := next, head := Function.update c.head j (work.onInt (c.head j))} := by
  rw [← selected] at table ⊢
  simpa only [advance_read B data c next work input auxiliary index] using
    Steps.single B data bits c _ _ _ _ _ _ _ table

theorem Steps.trans {data : InputData I A} {bits : BitString} {a b c : BankConfiguration O Q S k} {s t : ℕ}
    (left : B.Steps data bits a s b) (right : B.Steps data bits b t c) :
    B.Steps data bits a (s + t) c := by
  induction left with
  | refl => simpa using right
  | random a no yes bit s b table lookup rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.random a no yes bit (s + t) c table lookup (ih right)
  | step a next write work input auxiliary index emit s b table rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Steps.step a next write work input auxiliary index emit (s + t) c table (ih right)

theorem Steps.executes {data : InputData I A} {bits : BitString} {a b : BankConfiguration O Q S k} {s t : ℕ} {result : Outcome O}
    (path : B.Steps data bits a s b) (halt : B.Executes data bits b t result) :
    B.Executes data bits a (s + t) result := by
  induction path with
  | refl => simpa using halt
  | random a no yes bit s b table lookup rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Executes.random a no yes bit (s + t) result table lookup (ih halt)
  | step a next write work input auxiliary index emit s b table rest ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        Executes.step a next write work input auxiliary index emit (s + t) result table (ih halt)

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
