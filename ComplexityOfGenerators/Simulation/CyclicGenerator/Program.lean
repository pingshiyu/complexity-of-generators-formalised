import ComplexityOfGenerators.Simulation.CompositionMemory
import ComplexityOfGenerators.Simulation.TransducerBank.Space

/-!
# The cyclic enumeration program of Appendix A.17

Two virtual tapes hold the current word and the simulated decider's work.
The word is a little-endian counter over the finite alphabet. Only its current
letter is cached in finite control. A touched-cell flag permits the decider's
work interval to be erased and reused between candidates.

An accepted candidate is offered with probability one half. Declining it moves
to the next candidate. Overflow restarts enumeration if an accepted candidate
was seen, and otherwise drains the random tape. Output is delayed until the
selection coin succeeds, including when the candidate is the empty word.
-/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

@[ext] structure Cell (α : Type) (symbols : ℕ) where
  letter : Option α := none
  work : Option (Fin symbols) := none
  touched : Bool := false
  deriving Fintype

noncomputable section

local instance moveFintype : Fintype Move := Fintype.ofFinite _

inductive Phase (α : Type) (states : ℕ)
  | load
  | wordStart (seen : Bool)
  | input (q : Fin states) (seen : Bool)
  | mark (q : Fin states) (seen : Bool) (letter : Option α)
  | execute (q : Fin states) (seen : Bool) (letter : Option α)
  | moveInput (q : Fin states) (seen : Bool) (move : Move)
  | eraseLeft (seen : Bool)
  | eraseRight (seen : Bool)
  | workOrigin (seen : Bool)
  | counterOrigin (seen : Bool)
  | increment (seen : Bool)
  | outputOrigin
  | output
  | drain
  deriving Fintype

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

def alphabet : α ≃ Fin (Fintype.card α) := Fintype.equivFin α

def firstLetter : Option α :=
  if h : 0 < Fintype.card α then some (alphabet.symm ⟨0, h⟩) else none

def nextLetter (a : α) : Option α :=
  if h : (alphabet a).val + 1 < Fintype.card α then
    some (alphabet.symm ⟨(alphabet a).val + 1, h⟩) else none

abbrev State := Phase α D.states
abbrev Symbol := Cell α D.symbols
abbrev Config := TransducerBank.BankConfiguration α (State D) (Symbol D) 2

def select : State D → Fin 2
  | .mark _ _ _ | .execute _ _ _ | .eraseLeft _ | .eraseRight _ | .workOrigin _ => 1
  | _ => 0

def transition (phase : State D) (index : Option Unit) (origin : Bool) (cell : Symbol D) :
    TransducerBank.BankInstruction (State D) (Symbol D) α :=
  let step := fun q cell move emit => TransducerBank.BankInstruction.step q cell move .stay .stay .stay emit
  match phase with
  | .load => match index with
      | some _ => match firstLetter (α := α) with
          | some a => .step .load {cell with letter := some a} .right .stay .stay .right none
          | none => .readRandom .drain .drain
      | none => step (.wordStart false) cell .stay none
  | .wordStart seen =>
      step (if origin then .input D.initial seen else .wordStart seen) cell
        (if origin then .stay else .left) none
  | .input q seen => step (.mark q seen cell.letter) cell .stay none
  | .mark q seen letter => step (.execute q seen letter) {cell with touched := true} .stay none
  | .execute q seen letter => match D.transition q letter none none cell.work with
      | .accept => .readRandom .outputOrigin (.eraseLeft true)
      | .reject => step (.eraseLeft seen) cell .stay none
      | .readRandom _ _ => .readRandom .drain .drain
      | .step next write work input _ _ _ =>
          step (.moveInput next seen input)
            {cell with work := match write with | none => cell.work | some a => some a} work none
  | .moveInput q seen move =>
      step (.input q seen) cell (clampedReadMove origin cell.letter.isSome move) none
  | .eraseLeft seen =>
      if cell.touched then step (.eraseLeft seen) cell .left none
      else step (.eraseRight seen) cell .right none
  | .eraseRight seen =>
      if cell.touched then step (.eraseRight seen) {} .right none
      else step (.workOrigin seen) cell .left none
  | .workOrigin seen =>
      step (if origin then .counterOrigin seen else .workOrigin seen) cell
        (if origin then .stay else .left) none
  | .counterOrigin seen =>
      step (if origin then .increment seen else .counterOrigin seen) cell
        (if origin then .stay else .left) none
  | .increment seen => match cell.letter with
      | none => if seen then step (.wordStart false) cell .stay none else .readRandom .drain .drain
      | some a => match nextLetter a with
          | some b => step (.wordStart seen) {cell with letter := some b} .stay none
          | none => step (.increment seen) {cell with letter := firstLetter (α := α)} .right none
  | .outputOrigin =>
      step (if origin then .output else .outputOrigin) cell (if origin then .stay else .left) none
  | .output => match cell.letter with
      | some a => step .output cell .right (some a)
      | none => .accept
  | .drain => .readRandom .drain .drain

def bank : TransducerBank.TapeBank Unit Bool α (State D) (Symbol D) 2 where
  initial := .load
  blank := {}
  select := select D
  transition := fun q _ _ index origin cell => transition D q index origin cell

def machine : Machine Unit Bool α := TransducerBank.bankMachine (bank D)

/-- Even a malformed or unreachable state has no explicit rejection branch.
Source rejection advances enumeration; empty slices use exhaustion. -/
theorem transition_ne_reject (q : State D) (index : Option Unit) (origin : Bool) (cell : Symbol D) :
    transition D q index origin cell ≠ .reject := by
  cases q <;> simp [transition]
  all_goals repeat' first | split | simp_all

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
