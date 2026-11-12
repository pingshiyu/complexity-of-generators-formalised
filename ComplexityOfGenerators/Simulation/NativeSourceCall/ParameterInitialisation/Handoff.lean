import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.Execution
import ComplexityOfGenerators.Simulation.NativeSourceCall.Ready

namespace ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O]
    (M : Machine Unit Bool O) (parameter : F → Bool)

/-- The shared-tape source configuration obtained by changing only control at
preparation's accepting endpoint. The caller supplies the actual control
transfer when embedding the two finite routines. -/
def sourceConfiguration (c : Configuration (machine M parameter)) :
    Configuration (NativeSourceCall.machine (F := F) M) where
  state := NativeSourceCall.control M (.source M.initial)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

theorem sourceConfiguration_state (data : InputData Unit Bool) (fixed : ℤ → F) (length : ℕ)
    (c : Configuration (machine M parameter))
    (prepared : State M parameter data fixed {0} (packet length 0 0) .done 0 c) :
    NativeSourceCall.State M data fixed (fun _=>none) {0} (packet length 0 0)
      (.source M.initial) 0 (sourceConfiguration M parameter c) :=
  ⟨prepared.memory,rfl,prepared.head,
    ⟨prepared.bounds.input,prepared.bounds.auxiliary,prepared.bounds.index⟩⟩

theorem sourceConfiguration_ready (data : InputData Unit Bool) (fixed : ℤ → F) (length : ℕ)
    (c : Configuration (machine M parameter))
    (prepared : State M parameter data fixed {0} (packet length 0 0) .done 0 c) :
    Ready M data fixed length c.randomHead c.output M.initialConfiguration
      (sourceConfiguration M parameter c) :=
  ready_initial M data fixed length (sourceConfiguration M parameter c)
    (sourceConfiguration_state M parameter data fixed length c prepared)

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
