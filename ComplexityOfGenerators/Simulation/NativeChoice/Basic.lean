import ComplexityOfGenerators.Foundations.RunSimulation
import ComplexityOfGenerators.Foundations.ExecutionTranscripts
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.EquivFin

/-! A finite dispatch table combines native sources without interpreting their
work tapes or charging a simulation overhead. Each selected source retains its
own finite control and work alphabet. -/
namespace ComplexityOfGenerators.Simulation.NativeChoice
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] (family : E → Machine Unit Bool O)

abbrev Control := (event : E) × Fin (family event).states
abbrev Work := (event : E) × Fin (family event).symbols

def control : Control family ≃ Fin (Fintype.card (Control family)) := Fintype.equivFin _
def alphabet : Work family ≃ Fin (Fintype.card (Work family)) := Fintype.equivFin _

def encode (event : E) (symbol : Fin (family event).symbols) : Fin (Fintype.card (Work family)) :=
  alphabet family ⟨event,symbol⟩

def decode (event : E) (raw : Option (Fin (Fintype.card (Work family)))) :
    Option (Fin (family event).symbols) := by
  classical
  exact raw.bind fun symbol =>
    let packed := (alphabet family).symm symbol
    if same : packed.1=event then some (same ▸ packed.2) else none

@[simp] theorem decode_encode (event : E) (symbol : Option (Fin (family event).symbols)) :
    decode family event (symbol.map (encode family event))=symbol := by
  cases symbol with
  | none => rfl
  | some symbol =>
      dsimp only [decode,encode,Option.map,Option.bind]
      rw [(alphabet family).symm_apply_apply]
      simp

def instruction (event : E) : Instruction O (family event).states (family event).symbols →
    Instruction O (Fintype.card (Control family)) (Fintype.card (Work family))
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (control family ⟨event,no⟩) (control family ⟨event,yes⟩)
  | .step next write work input auxiliary index emit =>
      .step (control family ⟨event,next⟩) (write.map (encode family event)) work input auxiliary index emit

def start (event : E) : Fin (Fintype.card (Control family)) := control family ⟨event,(family event).initial⟩

def machine (event : E) : Machine Unit Bool O where
  inputFinite := (family event).inputFinite
  auxiliaryFinite := (family event).auxiliaryFinite
  outputFinite := (family event).outputFinite
  states := Fintype.card (Control family)
  symbols := Fintype.card (Work family)
  initial := start family event
  transition := fun q input auxiliary index raw =>
    let packed := (control family).symm q
    instruction family packed.1 ((family packed.1).transition packed.2 input auxiliary index (decode family packed.1 raw))

@[simp] theorem machine_transition (initial event : E) (q : Fin (family event).states) (input auxiliary index raw) :
    (machine family initial).transition (control family ⟨event,q⟩) input auxiliary index raw =
      instruction family event ((family event).transition q input auxiliary index (decode family event raw)) := by
  dsimp only [machine]
  rw [(control family).symm_apply_apply]

def configuration (event : E) (c : Configuration (family event)) : Configuration (machine family event) where
  state := control family ⟨event,c.state⟩
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  output := c.output
  workHead := c.workHead
  work := fun x => (c.work x).map (encode family event)
  visited := c.visited

def runState (event : E) : RunState (family event) → RunState (machine family event)
  | .running c => .running (configuration family event c)
  | .halted result => .halted result

@[simp] theorem configuration_initial (event : E) :
    configuration family event (family event).initialConfiguration = (machine family event).initialConfiguration := rfl

end
end ComplexityOfGenerators.Simulation.NativeChoice
