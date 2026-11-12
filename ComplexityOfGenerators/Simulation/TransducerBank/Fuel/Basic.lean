import ComplexityOfGenerators.Simulation.TransducerBank.Execution
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

/-!
# A genuine unary-clock controller for a finite tape bank

One extra tape carries clock marks. A source transition is cached in finite
control, one mark is checked, and only then is that transition committed. This
costs at most three bank transitions per source transition. The clock is not a
host-language fuel parameter to the transition table: its marks must be on a
real tape before entering this controller.

This module is only the bounded simulation component. Constructing those marks
from ordinary input is a separate charged computation; no general resource
characterisation is claimed merely from a preloaded clock configuration.
-/

namespace ComplexityOfGenerators.Simulation.TransducerBank.Fuel

noncomputable section
set_option synthInstance.maxSize 4096

local instance : Fintype Move := Fintype.ofFinite _

inductive Phase (Q S O : Type) (tapes : ℕ)
  | fetch (state : Q)
  | tickStep (selected : Fin tapes) (next : Q) (write : S)
      (work input auxiliary index : Move) (emit : Option O)
  | commit (selected : Fin tapes) (next : Q) (write : S)
      (work input auxiliary index : Move) (emit : Option O)
  | tickRandom (no yes : Q)
  | random (no yes : Q)
  deriving Fintype

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

abbrev Cell := S ⊕ Unit

def readSource : Cell (S := S) → S
  | .inl value => value
  | .inr _ => B.blank

def marked : Cell (S := S) → Bool
  | .inr _ => true
  | .inl _ => false

/-- Every instruction is finite-control, one-cell, and unit-head-movement. -/
def bank : TapeBank I A O (Phase Q S O k) (Cell (S := S)) (k + 1) where
  initial := .fetch B.initial
  blank := .inl B.blank
  select := fun phase => match phase with
    | .fetch state => (B.select state).castSucc
    | .commit selected _ _ _ _ _ _ _ => selected.castSucc
    | _ => Fin.last k
  transition := fun phase input auxiliary index origin cell => match phase with
    | .fetch state =>
        match B.transition state input auxiliary index origin (readSource B cell) with
        | .accept => .accept
        | .reject => .reject
        | .readRandom no yes =>
            .step (.tickRandom no yes) cell .stay .stay .stay .stay none
        | .step next write work input auxiliary index emit =>
            .step (.tickStep (B.select state) next write work input auxiliary index emit)
              cell .stay .stay .stay .stay none
    | .tickStep selected next write work input auxiliary index emit =>
        if marked cell then
          .step (.commit selected next write work input auxiliary index emit)
            cell .right .stay .stay .stay none
        else .reject
    | .commit _ next write work input auxiliary index emit =>
        .step (.fetch next) (.inl write) work input auxiliary index emit
    | .tickRandom no yes =>
        if marked cell then
          .step (.random no yes) cell .right .stay .stay .stay none
        else .reject
    | .random no yes => .readRandom (.fetch no) (.fetch yes)

def clockTape (fuel : ℕ) (position : ℤ) : Cell (S := S) :=
  if 0 ≤ position ∧ position < (fuel : ℤ) then .inr () else .inl B.blank

/-- This representation exposes the clock's physical contents and cursor. -/
def configuration (fuel used : ℕ) (source : BankConfiguration O Q S k) :
    BankConfiguration O (Phase Q S O k) (Cell (S := S)) (k + 1) :=
  ⟨.fetch source.state, source.inputHead, source.auxiliaryHead, source.indexHead,
    source.randomHead, source.output,
    Fin.lastCases (used : ℤ) source.head,
    Fin.lastCases (clockTape B fuel) (fun j position => .inl (source.tape j position))⟩

@[simp] theorem readSource_inl (value : S) : readSource B (.inl value) = value := rfl

@[simp] theorem clockTape_marked (fuel used : ℕ) :
    marked (clockTape B fuel used) = decide (used < fuel) := by
  by_cases inside : used < fuel <;> simp [clockTape, marked, inside]

end
end ComplexityOfGenerators.Simulation.TransducerBank.Fuel
