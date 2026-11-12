import ComplexityOfGenerators.Simulation.RandomMeter.Value
import ComplexityOfGenerators.Simulation.RejectDrain
import Mathlib.Data.Fintype.Prod

/-! A source ordinary step first consumes one ignored random bit. A source
random read consumes its actual choice bit. Consequently every source step has
random fuel, while ordinary/auxiliary inputs and the index are preserved. -/
namespace ComplexityOfGenerators.Simulation.RandomMeter
noncomputable section
variable {I A O : Type} (M : Machine I A O)

def control : (Bool × Fin M.states) ≃ Fin (Fintype.card (Bool × Fin M.states)) := Fintype.equivFin _

def direct : Instruction O M.states M.symbols →
    Instruction O (Fintype.card (Bool × Fin M.states)) M.symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (control M (false,no)) (control M (false,yes))
  | .step next write work input auxiliary index emit =>
      .step (control M (false,next)) write work input auxiliary index emit

def raw : Machine I A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  states := Fintype.card (Bool × Fin M.states)
  symbols := M.symbols
  initial := control M (false,M.initial)
  transition := fun state input auxiliary index cell =>
    let phase := (control M).symm state
    let action := M.transition phase.2 input auxiliary index cell
    if phase.1 then direct M action
    else match action with
      | .step _ _ _ _ _ _ _ => .readRandom (control M (true,phase.2)) (control M (true,phase.2))
      | _ => direct M action

def configuration (c : Configuration M) (position : ℕ) (execute : Bool := false) : Configuration (raw M) where
  state := control M (execute,c.state)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := position
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

/-- Rejection is converted to finite-tape exhaustion, so the compiled machine
is a halting transducer even when arbitrary source computations reject. -/
def machine : Machine I A O := rejectDrain (raw M)

@[simp] theorem configuration_initial : configuration M M.initialConfiguration 0=(raw M).initialConfiguration := rfl

end
end ComplexityOfGenerators.Simulation.RandomMeter
