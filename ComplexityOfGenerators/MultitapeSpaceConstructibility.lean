import ComplexityOfGenerators.MultitapeConstructibility
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

/-! Space constructibility is witnessed by an actual finite deterministic
machine on unary ordinary input. The radius bound counts visited positions on
its fixed work-tape bank, hence agrees within fixed constants with total work
cells. Output and readonly input are not work tapes. No time or final head
position convention is added to the witness. -/

namespace ComplexityOfGenerators.Multitape

/-- A charged deterministic unary computation of the available space. -/
structure SpaceConstructor (space : ℕ→ℕ) where
  machine : MultitapeMachine Unit Bool Unit
  deterministic : machine.Deterministic
  constant : ℕ
  constant_pos : 0<constant
  computes : ∀ n, machine.program.RegionRun (decisionData (List.replicate n ())) []
    (constant*(space n+1)) machine.initialConfiguration (.accepted (List.replicate (space n) ()))

def SpaceConstructible (space : ℕ→ℕ) : Prop := Nonempty (SpaceConstructor space)

namespace SpaceConstructor

variable {space : ℕ→ℕ} (constructor : SpaceConstructor space)

/-- The recorded computation is a genuine finite execution, including for
small inputs and a zero space value. -/
theorem executes (n : ℕ) : ∃ ticks,
    constructor.machine.Executes (decisionData (List.replicate n ())) []
      constructor.machine.initialConfiguration ticks (.accepted (List.replicate (space n) ())) :=
  (constructor.computes n).executes constructor.machine.program

end SpaceConstructor
end ComplexityOfGenerators.Multitape
