import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.RejectFree
import ComplexityOfGenerators.MultitapeModel

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

/-- One finite uniform program: bounded word proposal, direct source simulation,
and literal fallback. Its program reads the real unary index, not a host value. -/
def machine : MultitapeMachine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := source.inputFinite
  Control := Control source.program fallback
  Work := Cell source.Work α
  controlFinite := inferInstance
  workFinite := inferInstance
  tapes := source.tapes + 1
  program := bank source.program fallback

theorem noRejected (n : ℕ) (bits : BitString) (ticks : ℕ) :
    ¬ (machine source fallback).Executes (generatorData n) bits
      (machine source fallback).initialConfiguration ticks .rejected := by
  intro execution
  apply TapeBank.Executes.not_rejected (bank source.program fallback) ?_ execution rfl
  exact transition_ne_reject source.program fallback

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
