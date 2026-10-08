import ComplexityOfGenerators.Simulation.VirtualIndex
import ComplexityOfGenerators.Foundations.ResourceBounds
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Sum

/-!
# A native polynomial clock

The clock uses a fixed number of unary digit tracks, each ranging from zero to
the input length. The coefficient and the number of digits belong to finite
control; no unbounded counter is hidden in a machine state. A separate work
track holds the simulated machine's work tape. The source's read-only heads
move only when its saved instruction is executed.

This file defines the actual transition table. Its tape invariants and runtime
proofs are developed separately. In particular, the definition alone is not a
claim that a polynomial-time clock compiler has been proved correct.
-/

namespace ComplexityOfGenerators.Simulation

structure ClockCell (symbols digits : ℕ) where
  source : Option (Fin symbols)
  origin : Bool
  last : Bool
  digit : Fin digits → Bool
  workHead : Bool
  deriving DecidableEq, Fintype

instance {symbols digits : ℕ} : Inhabited (ClockCell symbols digits) :=
  ⟨⟨none, false, false, fun _ => false, false⟩⟩

noncomputable section

set_option synthInstance.maxSize 4096

local instance : Fintype Move := Fintype.ofFinite _

/-- Only nonhalting source instructions need to be saved during a clock tick. -/
inductive ClockAction (O : Type) (states symbols : ℕ)
  | random (no yes : Fin states)
  | step (next : Fin states) (write : Option (Fin symbols))
      (work input auxiliary index : Move) (emit : Option O)
  deriving Fintype

inductive ClockPhase (O : Type) (states symbols coefficient digits : ℕ)
  | source (q : Fin states) (negative : Bool) (remaining : Fin (coefficient + 1))
  | toOrigin (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1))
  | carry (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1)) (digit : Fin (digits + 1))
  | seek (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1)) (digit : Fin digits)
  | reset (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1)) (digit : Fin digits)
  | place (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1)) (digit : Fin digits)
  | back (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1))
  | returnWork (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1))
  | execute (action : ClockAction O states symbols) (negative : Bool)
      (remaining : Fin (coefficient + 1))
  | placeWork (q : Fin states) (negative : Bool) (remaining : Fin (coefficient + 1))
  deriving Fintype

variable {I A O : Type} [Fintype O] (M : Machine I A O) (p : PolynomialBound)

def clockAlphabet : ClockCell M.symbols p.degree ≃
    Fin (Fintype.card (ClockCell M.symbols p.degree)) := Fintype.equivFin _

def clockControl : ClockPhase O M.states M.symbols p.coefficient p.degree ≃
    Fin (Fintype.card (ClockPhase O M.states M.symbols p.coefficient p.degree)) :=
  Fintype.equivFin _

def clockRead (raw : Option (Fin (Fintype.card (ClockCell M.symbols p.degree) + 1))) :
    ClockCell M.symbols p.degree := bootDecode (clockAlphabet M p) raw

def clockWrite (cell : ClockCell M.symbols p.degree) :
    Fin (Fintype.card (ClockCell M.symbols p.degree) + 1) := bootEncode (clockAlphabet M p) cell

omit [Fintype O] in
@[simp] theorem clockRead_write (cell : ClockCell M.symbols p.degree) :
    clockRead M p (some (clockWrite M p cell)) = cell := bootDecode_encode _ _

def clockTransition (phase : ClockPhase O M.states M.symbols p.coefficient p.degree)
    (input : Option I) (auxiliary : Option A) (index : Option Bool)
    (raw : Option (Fin (Fintype.card (ClockCell M.symbols p.degree) + 1))) :
    Instruction O (Fintype.card (ClockPhase O M.states M.symbols p.coefficient p.degree))
      (Fintype.card (ClockCell M.symbols p.degree) + 1) :=
  let cell := clockRead M p raw
  let silent := fun phase move =>
    Instruction.step (clockControl M p phase) none move .stay .stay .stay none
  let write := fun phase cell move =>
    Instruction.step (clockControl M p phase) (some (clockWrite M p cell))
      move .stay .stay .stay none
  match phase with
  | .source q negative remaining =>
      match M.transition q input auxiliary index cell.source with
      | .accept => .accept
      | .reject => .reject
      | .readRandom no yes =>
          if remaining.val = 0 then .reject
          else silent (.toOrigin (.random no yes) negative remaining) .stay
      | .step next symbol work inputMove auxiliaryMove indexMove emit =>
          if remaining.val = 0 then .reject
          else silent (.toOrigin (.step next symbol work inputMove auxiliaryMove indexMove emit)
            negative remaining) .stay
  | .toOrigin action negative remaining =>
      if cell.origin then silent (.carry action negative remaining ⟨0, Nat.zero_lt_succ _⟩) .stay
      else silent phase (if negative then .right else .left)
  | .carry action negative remaining digit =>
      if h : digit.val < p.degree then
        silent (.seek action negative remaining ⟨digit.val, h⟩) .stay
      else silent (.returnWork action negative ⟨remaining.val - 1, by omega⟩) .stay
  | .seek action negative remaining digit =>
      if !cell.digit digit then silent phase .right
      else if cell.last then
        write (.reset action negative remaining digit)
          {cell with digit := Function.update cell.digit digit false} .stay
      else write (.place action negative remaining digit)
          {cell with digit := Function.update cell.digit digit false} .right
  | .reset action negative remaining digit =>
      if cell.origin then
        write (.carry action negative remaining ⟨digit.val + 1, by omega⟩)
          {cell with digit := Function.update cell.digit digit true} .stay
      else silent phase .left
  | .place action negative remaining digit =>
      write (.back action negative remaining)
        {cell with digit := Function.update cell.digit digit true} .stay
  | .back action negative remaining =>
      if cell.origin then silent (.returnWork action negative remaining) .stay
      else silent phase .left
  | .returnWork action negative remaining =>
      if cell.workHead then silent (.execute action negative remaining) .stay
      else silent phase (if negative then .left else .right)
  | .execute action negative remaining =>
      match action with
      | .random no yes => .readRandom
          (clockControl M p (.source no negative remaining))
          (clockControl M p (.source yes negative remaining))
      | .step next symbol work inputMove auxiliaryMove indexMove emit =>
          let side := if cell.origin then decide (work = .left) else negative
          .step (clockControl M p (.placeWork next side remaining))
            (some (clockWrite M p {cell with
              source := match symbol with | none => cell.source | some a => some a
              workHead := false})) work inputMove auxiliaryMove indexMove emit
  | .placeWork q negative remaining =>
      write (.source q negative remaining) {cell with workHead := true} .stay

def polynomialClockRoutine : Routine I A O (Fintype.card (ClockCell M.symbols p.degree) + 1) where
  states := Fintype.card (ClockPhase O M.states M.symbols p.coefficient p.degree)
  initial := clockControl M p (.source M.initial false ⟨p.coefficient, by omega⟩)
  transition := fun state => clockTransition M p ((clockControl M p).symm state)

abbrev polynomialClockCore [Finite I] [Finite A] := (polynomialClockRoutine M p).machine

def polynomialClockCell (length : ℕ) (work : ℤ → Option (Fin M.symbols))
    (digits : Fin p.degree → Option ℤ) (workHead : Option ℤ) (i : ℤ) :
    ClockCell M.symbols p.degree where
  source := work i
  origin := decide (i = 0)
  last := decide (i = (length : ℤ))
  digit := fun j => decide (digits j = some i)
  workHead := decide (workHead = some i)

def PolynomialClockMemory (length : ℕ) (work : ℤ → Option (Fin M.symbols))
    (digits : Fin p.degree → Option ℤ) (workHead : Option ℤ)
    (memory : ℤ → Option (Fin (Fintype.card (ClockCell M.symbols p.degree) + 1))) : Prop :=
  ∀ i, clockRead M p (memory i) = polynomialClockCell M p length work digits workHead i

end

end ComplexityOfGenerators.Simulation
