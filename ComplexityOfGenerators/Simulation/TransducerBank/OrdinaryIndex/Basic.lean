import ComplexityOfGenerators.Simulation.TransducerBank.Execution
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Option

/-! An actual materialized length index for an arbitrary fixed finite bank.
One extra work tape stores unary marks. An initial scan writes one mark per
ordinary input symbol, then rewinds. Source work/index accesses are split into
finite lookup/inspect/commit phases. This construction is intended for TIME
bounds ≥n; materializing n marks is deliberately not a logarithmic-space claim. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex

noncomputable section
set_option synthInstance.maxSize 4096

local instance : Fintype Move := Fintype.ofFinite _

inductive Phase (Q S : Type) (tapes : ℕ)
  | load | rewind
  | fetch (state : Q)
  | inspect (state : Q) (sourceOrigin : Bool) (value : S)
  | commit (selected : Fin tapes) (state : Q) (write : S) (move : Move)
  deriving Fintype

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

abbrev Cell := S ⊕ Unit

def readWork : Cell (S := S) → S
  | .inl value => value
  | .inr _ => B.blank

def readIndex : Cell (S := S) → Option Unit
  | .inl _ => none
  | .inr _ => some ()

def indexMove (move : Move) (origin : Bool) (cell : Cell (S := S)) : Move :=
  match move with
  | .left => if origin then .stay else .left
  | .stay => .stay
  | .right => if (readIndex cell).isSome then .right else .stay

def bank : TapeBank I A O (Phase Q S k) (Cell (S := S)) (k + 1) where
  initial := .load
  blank := .inl B.blank
  select := fun phase => match phase with
    | .fetch state => (B.select state).castSucc
    | .commit selected _ _ _ => selected.castSucc
    | _ => Fin.last k
  transition := fun phase input auxiliary _ origin cell => match phase with
    | .load => if input.isSome then .step .load (.inr ()) .right .right .stay .stay none
        else .step .rewind cell .stay .stay .stay .stay none
    | .rewind => if origin then .step (.fetch B.initial) cell .stay .stay .stay .stay none
        else .step .rewind cell .left .left .stay .stay none
    | .fetch state => .step (.inspect state origin (readWork B cell)) cell .stay .stay .stay .stay none
    | .inspect state sourceOrigin value =>
        match B.transition state input auxiliary (readIndex cell) sourceOrigin value with
        | .accept => .accept
        | .reject => .reject
        | .readRandom no yes => .readRandom (.fetch no) (.fetch yes)
        | .step next write work input auxiliary index emit =>
            .step (.commit (B.select state) next write work) cell
              (indexMove index origin cell) input auxiliary .stay emit
    | .commit _ state write move =>
        .step (.fetch state) (.inl write) move .stay .stay .stay none

def sourceData (data : InputData I A) : InputData I A :=
  {data with index := data.input.length}

def indexTape (length : ℕ) (position : ℤ) : Cell (S := S) :=
  if 0 ≤ position ∧ position < (length : ℤ) then .inr () else .inl B.blank

def configuration (data : InputData I A) (source : BankConfiguration O Q S k) :
    BankConfiguration O (Phase Q S k) (Cell (S := S)) (k + 1) :=
  ⟨.fetch source.state, source.inputHead, source.auxiliaryHead, 0, source.randomHead, source.output,
    Fin.lastCases (source.indexHead : ℤ) source.head,
    Fin.lastCases (indexTape B data.input.length) (fun j p => .inl (source.tape j p))⟩

def inspecting (data : InputData I A) (source : BankConfiguration O Q S k) :
    BankConfiguration O (Phase Q S k) (Cell (S := S)) (k + 1) :=
  {configuration B data source with state := (.inspect source.state
    (decide (source.head (B.select source.state) = 0))
    (source.tape (B.select source.state) (source.head (B.select source.state))))}

end
end ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex
