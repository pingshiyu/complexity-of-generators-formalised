import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Words
import ComplexityOfGenerators.Simulation.TransducerBank.Rewind

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter

set_option backward.isDefEq.respectTransparency false

inductive Phase | carry | rewind | done
  deriving DecidableEq,Fintype

def transition {I A O : Type} (phase : Phase) (_ : Option I) (_ : Option A) (_ : Option Unit)
    (origin : Bool) (symbol : Option Bool) : BankInstruction Phase (Option Bool) O :=
  match phase with
  | .done => .accept
  | .carry => if symbol=some true then
      .step .carry (some false) .right .stay .stay .stay none
    else .step .rewind (some true) .stay .stay .stay .stay none
  | .rewind => .step (if origin then .done else .rewind) symbol
      (if origin then .stay else .left) .stay .stay .stay none

/-- A concrete binary ripple-carry controller on one selected work tape. -/
def bank (I A O : Type) : TapeBank I A O Phase (Option Bool) 1 where
  initial := .carry
  blank := none
  select := fun _ => 0
  transition := transition

def digitTape (bits : List Bool) (position : ℤ) : Option Bool :=
  if 0≤position then bits[position.toNat]? else none

def encoded {O : Type} (bits : List Bool) (position : ℕ) (phase : Phase) :
    BankConfiguration O Phase (Option Bool) 1 :=
  ⟨phase,0,0,0,0,[],fun _ => position,fun _ => digitTape bits⟩

theorem initial_encoded (I A O : Type) : (bank I A O).initialConfiguration=encoded [] 0 .carry := by
  apply BankConfiguration.ext <;> try rfl
  funext j position
  simp [encoded,digitTape,TapeBank.initialConfiguration,bank]

theorem deterministic (I A O : Type) : (bank I A O).Deterministic := by
  intro phase input auxiliary index origin symbol
  cases phase <;> by_cases good : symbol=some true <;> simp [bank,transition,good]

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter
