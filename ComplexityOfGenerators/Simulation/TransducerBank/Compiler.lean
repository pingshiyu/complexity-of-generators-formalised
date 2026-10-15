import ComplexityOfGenerators.Simulation.TransducerBank.Basic

/-! A native finite-control compiler for a fixed finite bank of tapes. All
virtual head movements are implemented by scans of the single native work
tape. The tape bank is an intermediate language, not a replacement for the
machine model used in the complexity classes. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank

@[ext] structure BankCell (S : Type) (k : ℕ) where
  symbol : Fin k → S
  marked : Fin k → Bool
  origin : Bool
  deriving Fintype

inductive BankPhase (Q : Type) (k : ℕ)
  | boot
  | seek (q : Q) (negative : Fin k → Bool)
  | place (q : Q) (negative : Fin k → Bool) (j : Fin k)
  | back (q : Q) (negative : Fin k → Bool) (side : Bool)
  deriving Fintype

noncomputable section

set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

def bankAlphabet : BankCell S k ≃ Fin (Fintype.card (BankCell S k)) := Fintype.equivFin _
def bankControl : BankPhase Q k ≃ Fin (Fintype.card (BankPhase Q k)) := Fintype.equivFin _

def bankBlank : BankCell S k := ⟨fun _ => B.blank, fun _ => false, false⟩

def bankRead (raw : Option (Fin (Fintype.card (BankCell S k)))) : BankCell S k :=
  match raw with | none => bankBlank B | some a => bankAlphabet.symm a

@[simp] theorem bankRead_write (cell : BankCell S k) :
    bankRead B (some (bankAlphabet cell)) = cell := by simp [bankRead]

def bankSide (origin negative : Bool) (move : Move) : Bool :=
  if origin then decide (move = .left) else negative

def bankTransition (phase : BankPhase Q k) (input : Option I) (auxiliary : Option A) (index : Option Unit)
    (raw : Option (Fin (Fintype.card (BankCell S k)))) :
    Instruction O (Fintype.card (BankPhase Q k)) (Fintype.card (BankCell S k)) :=
  let cell := bankRead B raw
  let silent := fun phase move => Instruction.step (bankControl phase) none move .stay .stay .stay none
  match phase with
  | .boot => .step (bankControl (.seek B.initial (fun _ => false)))
      (some (bankAlphabet ⟨fun _ => B.blank, fun _ => true, true⟩)) .stay .stay .stay .stay none
  | .seek q negative =>
      let j := B.select q
      if !cell.marked j then silent phase (if negative j then .left else .right)
      else match B.transition q input auxiliary index cell.origin (cell.symbol j) with
      | .accept => .accept
      | .reject => .reject
      | .readRandom no yes => .readRandom
          (bankControl (.back no negative (negative j))) (bankControl (.back yes negative (negative j)))
      | .step next write work input auxiliary index emit =>
          .step (bankControl (.place next
            (Function.update negative j (bankSide cell.origin (negative j) work)) j))
            (some (bankAlphabet {cell with
              symbol := Function.update cell.symbol j write,
              marked := Function.update cell.marked j false})) work input auxiliary index emit
  | .place q negative j =>
      .step (bankControl (.back q negative (negative j)))
        (some (bankAlphabet {cell with marked := Function.update cell.marked j true}))
        .stay .stay .stay .stay none
  | .back q negative side =>
      if cell.origin then silent (.seek q negative) .stay
      else silent phase (if side then .right else .left)

def bankMachine : Machine I A O where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := Fintype.card (BankPhase Q k)
  symbols := Fintype.card (BankCell S k)
  initial := bankControl .boot
  transition := fun q input auxiliary index raw => bankTransition B (bankControl.symm q) input auxiliary index raw

theorem bankMachine_deterministic (B : TapeBank I A O Q S k) (h : B.Deterministic) :
    (bankMachine B).Deterministic := by
  intro q input auxiliary index raw
  dsimp only [bankMachine]
  cases phase : (bankControl (Q := Q) (k := k)).symm q with
  | boot => trivial
  | place q negative j => trivial
  | back q negative side => cases h : (bankRead B raw).origin <;> simp [bankTransition, h]
  | seek q negative =>
      cases marked : (bankRead B raw).marked (B.select q)
      · simp [bankTransition, marked]
      · have deterministic := h q input auxiliary index (bankRead B raw).origin
          ((bankRead B raw).symbol (B.select q))
        cases action : B.transition q input auxiliary index (bankRead B raw).origin
            ((bankRead B raw).symbol (B.select q)) <;>
          simp_all [bankTransition]


def bankCell (tape : Fin k → ℤ → S) (head : Fin k → Option ℤ) (i : ℤ) : BankCell S k :=
  ⟨fun j => tape j i, fun j => decide (head j = some i), decide (i = 0)⟩

def BankMemory (tape : Fin k → ℤ → S) (head : Fin k → Option ℤ)
    (memory : ℤ → Option (Fin (Fintype.card (BankCell S k)))) : Prop :=
  ∀ i, bankRead B (memory i) = bankCell tape head i

theorem BankMemory.write_clear {tape : Fin k → ℤ → S} {head : Fin k → Option ℤ}
    {memory} (j : Fin k) (position : ℤ) (symbol : S)
    (h : BankMemory B tape head memory) (atHead : head j = some position) :
    BankMemory B (Function.update tape j (Function.update (tape j) position symbol))
      (Function.update head j none)
      (Function.update memory position (some (bankAlphabet
        {bankRead B (memory position) with
          symbol := Function.update (bankRead B (memory position)).symbol j symbol,
          marked := Function.update (bankRead B (memory position)).marked j false}))) := by
  intro i
  by_cases same : i = position
  · subst i
    rw [Function.update_self, bankRead_write, h]
    apply BankCell.ext
    · funext a
      by_cases ha : a = j <;> simp [bankCell, ha]
    · funext a
      by_cases ha : a = j <;> simp [bankCell, ha]
    · rfl
  · rw [Function.update_of_ne same, h]
    apply BankCell.ext
    · funext a
      by_cases ha : a = j <;> simp [bankCell, ha, same]
    · funext a
      by_cases ha : a = j <;> simp [bankCell, ha, atHead, Ne.symm same]
    · rfl

theorem BankMemory.place {tape : Fin k → ℤ → S} {head : Fin k → Option ℤ}
    {memory} (j : Fin k) (position : ℤ)
    (h : BankMemory B tape head memory) (absent : head j = none) :
    BankMemory B tape (Function.update head j (some position))
      (Function.update memory position (some (bankAlphabet
        {bankRead B (memory position) with
          marked := Function.update (bankRead B (memory position)).marked j true}))) := by
  intro i
  by_cases same : i = position
  · subst i
    rw [Function.update_self, bankRead_write, h]
    apply BankCell.ext
    · rfl
    · funext a
      by_cases ha : a = j <;> simp [bankCell, ha]
    · rfl
  · rw [Function.update_of_ne same, h]
    apply BankCell.ext
    · rfl
    · funext a
      by_cases ha : a = j <;> simp [bankCell, ha, absent, Ne.symm same]
    · rfl

structure BankSnapshot (source : BankConfiguration O Q S k)
    (target : Configuration (bankMachine B)) : Prop where
  memory : BankMemory B source.tape (fun j => some (source.head j)) target.work
  input : target.inputHead = source.inputHead
  auxiliary : target.auxiliaryHead = source.auxiliaryHead
  index : target.indexHead = source.indexHead
  random : target.randomHead = source.randomHead
  output : target.output = source.output

structure BankReady (source : BankConfiguration O Q S k) (negative : Fin k → Bool)
    (target : Configuration (bankMachine B)) : Prop extends BankSnapshot B source target where
  state : target.state = bankControl (.seek source.state negative)
  head : target.workHead = 0
  side : ∀ j, if negative j then source.head j ≤ 0 else 0 ≤ source.head j

theorem BankSnapshot.readHeadBounds {data : InputData I A} {r : ℕ} {source} {target}
    (h : BankSnapshot B source target) (bounded : B.Bounded data r source) :
    ReadHeadBounds (bankMachine B) data target := by
  constructor
  · simpa [h.input] using bounded.input
  · simpa [h.auxiliary] using bounded.auxiliary
  · simpa [h.index] using bounded.index

theorem BankSnapshot.scan {source} {start ready : Configuration (bankMachine B)} {position}
    (h : BankSnapshot B source start) (scan : ScanResult (bankMachine B) start ready position) :
    BankSnapshot B source ready := by
  exact ⟨scan.memory ▸ h.memory, scan.input.trans h.input,
    scan.auxiliary.trans h.auxiliary, scan.index.trans h.index,
    scan.random.trans h.random, scan.output.trans h.output⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank
