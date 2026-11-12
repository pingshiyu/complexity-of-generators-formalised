import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Paths
import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.State

/-! The two native continuation edges between actual preparation, source replay,
and the suspended controller. They preserve physical random/output cursors. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

@[simp] theorem selected_read (event : E) (raw) :
    NativeSourceCall.read (F:=Fixed C) (selectedSource M start event) raw=NativeSourceCall.read M raw := rfl

def callConfiguration (event : E)
    (c : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event))) :
    Configuration (NativeSourceCall.machine (F:=Fixed C) (selectedSource M start event)) where
  state := NativeSourceCall.control (selectedSource M start event) (.source (start event))
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := insert c.workHead c.visited
  output := c.output

theorem call_prepared (event : E) (data : InputData Unit Bool) (fixed : ℤ → Fixed C) (length : ℕ)
    (c : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event)))
    (prepared : ParameterInitialisation.State M (parameter event) data fixed {0} (packet length 0 0) .done 0 c) :
    NativeSourceCall.State (selectedSource M start event) data fixed (fun _=>none) {0} (packet length 0 0)
      (.source (selectedSource M start event).initial) 0 (callConfiguration C M parameter start event c) := by
  refine ⟨?_,rfl,prepared.head,⟨prepared.bounds.input,prepared.bounds.auxiliary,prepared.bounds.index⟩⟩
  intro position
  change NativeSourceCall.read (selectedSource M start event) (c.work position)=_
  rw [selected_read]
  exact prepared.memory position

theorem prepare_handoff (resume : Fin C.states) (event : E) (data : InputData Unit Bool) (bits : BitString)
    (c : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event)))
    (state : c.state=ParameterInitialisation.control .done)
    (bounds : ReadHeadBounds (ParameterInitialisation.machine M (parameter event)) data c) :
    (machine C M parameter start).Steps data bits (prepareConfiguration C M parameter start resume event c) 1
      (sourceConfiguration C M parameter start resume event (callConfiguration C M parameter start event c)) := by
  apply Machine.Steps.tail .refl
  have mappedState : (prepareConfiguration C M parameter start resume event c).state=
      control C M (.prepare resume event .done) := by
    simp only [prepareConfiguration,RoutineEmbedding.configuration,prepareControl,state,Equiv.symm_apply_apply]
  have table : (machine C M parameter start).transition
      (prepareConfiguration C M parameter start resume event c).state
      data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead)=
      .step (control C M (.source resume event (.source (start event)))) none .stay .stay .stay .stay none := by
    rw [mappedState,machine_transition]
    rfl
  change (machine C M parameter start).next data bits (prepareConfiguration C M parameter start resume event c)=_
  rw [(machine C M parameter start).next_step data bits _ _ _ _ _ _ _ _ table]
  simp only [Machine.stepConfiguration,prepareConfiguration,sourceConfiguration,RoutineEmbedding.configuration,
    callConfiguration,sourceControl,selected_control,Move.onInt,Move.onInput,
    Nat.min_eq_left bounds.input,Nat.min_eq_left bounds.auxiliary,Nat.min_eq_left bounds.index]
  exact congrArg (fun phase : NativeSourceCall.Phase O M.states M.symbols =>
    RunState.running ({
      state:=control C M (.source resume event phase)
      inputHead:=c.inputHead
      auxiliaryHead:=c.auxiliaryHead
      indexHead:=c.indexHead
      randomHead:=c.randomHead
      workHead:=c.workHead
      work:=c.work
      visited:=insert c.workHead c.visited
      output:=c.output} : Configuration (machine C M parameter start)))
    ((NativeSourceCall.control M).symm_apply_apply (.source (start event))).symm

def resumedConfiguration (resume : Fin C.states) (event : E)
    (c : Configuration (NativeSourceCall.machine (F:=Fixed C) (selectedSource M start event))) :
    Configuration (machine C M parameter start) where
  state := control C M (.controller resume)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := insert c.workHead c.visited
  output := c.output

theorem source_handoff (resume : Fin C.states) (event : E) (data : InputData Unit Bool) (bits : BitString)
    (c : Configuration (NativeSourceCall.machine (F:=Fixed C) (selectedSource M start event)))
    (state : c.state=NativeSourceCall.control (selectedSource M start event) .done)
    (bounds : ReadHeadBounds (NativeSourceCall.machine (selectedSource M start event)) data c) :
    (machine C M parameter start).Steps data bits (sourceConfiguration C M parameter start resume event c) 1
      (resumedConfiguration C M parameter start resume event c) := by
  apply Machine.Steps.tail .refl
  have mappedState : (sourceConfiguration C M parameter start resume event c).state=
      control C M (.source resume event .done) := by
    simp only [sourceConfiguration,RoutineEmbedding.configuration,sourceControl,state,selected_control]
    change control C M (.source resume event ((NativeSourceCall.control M).symm ((NativeSourceCall.control M) .done))) = _
    exact congrArg (fun phase=>control C M (.source resume event phase)) ((NativeSourceCall.control M).symm_apply_apply _)
  have table : (machine C M parameter start).transition
      (sourceConfiguration C M parameter start resume event c).state
      data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead)=
      .step (control C M (.controller resume)) none .stay .stay .stay .stay none := by
    rw [mappedState,machine_transition]
    rfl
  change (machine C M parameter start).next data bits (sourceConfiguration C M parameter start resume event c)=_
  rw [(machine C M parameter start).next_step data bits _ _ _ _ _ _ _ _ table]
  simp only [Machine.stepConfiguration,sourceConfiguration,resumedConfiguration,RoutineEmbedding.configuration,
    Move.onInt,Move.onInput,Nat.min_eq_left bounds.input,Nat.min_eq_left bounds.auxiliary,Nat.min_eq_left bounds.index]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
