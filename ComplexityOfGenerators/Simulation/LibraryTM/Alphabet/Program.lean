import ComplexityOfGenerators.Simulation.LibraryTM.Native
import ComplexityOfGenerators.Simulation.NativeNTM.Encoding

/-! Feed a library decider with the bounded unary encoding of an arbitrary
finite-alphabet word. After copying, the original library compiler is reused. -/

namespace ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] {n : ℕ} (M : Complexity.TM n)

inductive Phase (Q : Type) (a : ℕ)
  | start | load | emit (zeros : Fin (a + 1)) | rewind | run (state : Q)
  deriving Fintype

abbrev State := Phase (LibraryTM.State M) (Fintype.card α)
abbrev Config := BankConfiguration Unit (State (α := α) M) Complexity.Γ (n + 2)

def liftInstruction : BankInstruction (LibraryTM.State M) Complexity.Γ Unit →
    BankInstruction (State (α := α) M) Complexity.Γ Unit
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (.run no) (.run yes)
  | .step q w work input auxiliary index emit => .step (.run q) w work input auxiliary index emit

def select : State (α := α) M → Fin (n + 2)
  | .run q => LibraryTM.select M q
  | _ => 0

def transition (q : State (α := α) M) (input : Option α) (origin : Bool) (cell : Complexity.Γ) :
    BankInstruction (State (α := α) M) Complexity.Γ Unit :=
  let go := fun q d => BankInstruction.step q cell d .stay .stay .stay none
  match q with
  | .start => go .load .right
  | .load => match input with
    | none => go .rewind .stay
    | some a => go (.emit ⟨(Fintype.equivFin α a).val, by have := (Fintype.equivFin α a).isLt; omega⟩) .stay
  | .emit k => if h : k.val = 0 then .step .load .one .right .right .stay .stay none
      else .step (.emit ⟨k.val - 1, by omega⟩) .zero .right .stay .stay .stay none
  | .rewind => go (if origin then .run (ready M M.qstart) else .rewind) (if origin then .stay else .left)
  | .run q => liftInstruction M (LibraryTM.transition M q none origin cell)

def bank : TapeBank α Bool Unit (State (α := α) M) Complexity.Γ (n + 2) where
  initial := .start
  blank := .blank
  select := select M
  transition := fun q input _ _ origin cell => transition M q input origin cell

theorem deterministic : (bank (α := α) M).Deterministic := by
  intro q input auxiliary index origin cell
  cases q with
  | run q =>
    have h := LibraryTM.deterministic M q none none none origin cell
    dsimp [LibraryTM.bank] at h
    simp only [bank, transition]
    cases act : LibraryTM.transition M q none origin cell <;> simpa [liftInstruction, act] using h
  | start => trivial
  | load => cases input <;> trivial
  | emit k => simp only [bank, transition]; split_ifs <;> trivial
  | rewind => trivial

/-- In the original compiler all physical input movement ends once the input
is exhausted. The library's moving input head is on a charged virtual tape. -/
theorem exhausted_stays (q : LibraryTM.State M) (origin : Bool) (cell : Complexity.Γ)
    (next write work input auxiliary index emit)
    (table : LibraryTM.transition M q none origin cell = .step next write work input auxiliary index emit) :
    input = .stay := by
  cases q <;> simp only [LibraryTM.transition] at table
  all_goals try split_ifs at table
  all_goals cases table <;> rfl

def lift (word : List α) (c : LibraryTM.Config M) : Config (α := α) M :=
  ⟨.run c.state, word.length, c.auxiliaryHead, c.indexHead, c.randomHead, c.output, c.head, c.tape⟩

theorem lift_instruction (word : List α) (full : BitString) (c : LibraryTM.Config M)
    (endInput : c.inputHead = full.length) :
    (bank M).instruction (decisionData word) (lift M word c) =
      liftInstruction M ((LibraryTM.bank M).instruction (decisionData full) c) := by
  simp [TapeBank.instruction, bank, transition, lift, select, LibraryTM.bank, decisionData, endInput]

theorem lift_bounded (word : List α) (full : BitString) (r : ℕ) (c : LibraryTM.Config M)
    (bound : (LibraryTM.bank M).Bounded (decisionData full) r c) :
    (bank M).Bounded (decisionData word) r (lift M word c) :=
  ⟨le_rfl, bound.auxiliary, bound.index, bound.head⟩

theorem lift_advance (word : List α) (full : BitString) (c : LibraryTM.Config M)
    (next write work auxiliary index emit) :
    (bank M).advance (decisionData word) (lift M word c) (.run next) write work .stay auxiliary index emit =
      lift M word ((LibraryTM.bank M).advance (decisionData full) c next write work .stay auxiliary index emit) := by
  apply BankConfiguration.ext <;> simp [TapeBank.advance, lift, bank, select, LibraryTM.bank, Move.onInput, decisionData]

end
end ComplexityOfGenerators.Simulation.LibraryTM.Alphabet
