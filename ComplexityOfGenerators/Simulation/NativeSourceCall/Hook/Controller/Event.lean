import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Basic
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Paths

/-! A native controller event is executed, with its output suppressed, before
the genuinely updated fixed track is passed to packet preparation. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

def preparationOf (event : E) (c : Configuration (machine C M parameter start)) :
    Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event)) :=
  ⟨ParameterInitialisation.control .first,c.inputHead,c.auxiliaryHead,c.indexHead,c.randomHead,
    c.workHead,c.work,c.visited,c.output⟩

theorem preparationOf_eq (resume : Fin C.states) (event : E) (c : Configuration (machine C M parameter start))
    (state : c.state=control C M (.prepare resume event .first)) :
    prepareConfiguration C M parameter start resume event (preparationOf C M parameter start event c)=c := by
  cases c
  simp only [prepareConfiguration,preparationOf,RoutineEmbedding.configuration,prepareControl,Equiv.symm_apply_apply] at state ⊢
  cases state
  rfl

theorem event_step (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
    (source : Configuration C) (target : Configuration (machine C M parameter start))
    (ready : ControllerReady C M parameter start data origin source target)
    (resume : Fin C.states) (write : Option (Fin C.symbols)) (event : E)
    (atOrigin : source.workHead=0)
    (action : C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead)=
      .step resume write .stay .stay .stay .stay (some event)) :
    ∃ prepared : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event)),
      (machine C M parameter start).Steps data bits target 1 (prepareConfiguration C M parameter start resume event prepared) ∧
      ParameterInitialisation.BlankMemory M
        (C.stepConfiguration data source resume write .stay .stay .stay .stay (some event)).work origin prepared.work ∧
      prepared.state=ParameterInitialisation.control .first ∧ prepared.workHead=0 ∧
      ReadHeadBounds (ParameterInitialisation.machine M (parameter event)) data prepared ∧
      prepared.randomHead=source.randomHead ∧ prepared.output=target.output ∧
      prepared.inputHead=(C.stepConfiguration data source resume write .stay .stay .stay .stay (some event)).inputHead ∧
      prepared.auxiliaryHead=(C.stepConfiguration data source resume write .stay .stay .stay .stay (some event)).auxiliaryHead ∧
      prepared.indexHead=(C.stepConfiguration data source resume write .stay .stay .stay .stay (some event)).indexHead := by
  let cell := read M (target.work target.workHead)
  let next : Configuration (machine C M parameter start) :=
    (machine C M parameter start).stepConfiguration data target (control C M (.prepare resume event .first))
      (write.map (fun symbol=>alphabet M {cell with fixed:=some symbol})) .stay .stay .stay .stay none
  let prepared := preparationOf C M parameter start event next
  have table : (machine C M parameter start).transition target.state data.input[target.inputHead]?
      data.auxiliary[target.auxiliaryHead]? (if target.indexHead<data.index then some () else none) (target.work target.workHead)=
      .step (control C M (.prepare resume event .first))
        (write.map (fun symbol=>alphabet M {cell with fixed:=some symbol})) .stay .stay .stay .stay none := by
    rw [ready.state,machine_transition,ready.input,ready.auxiliary,ready.index,ready.head]
    simp only [transition,ready.memory source.workHead,action,cell,ready.head]
  have path : (machine C M parameter start).Steps data bits target 1 next :=
    Machine.Steps.tail .refl ((machine C M parameter start).next_step data bits target _ _ _ _ _ _ _ table)
  refine ⟨prepared,?_,?_,rfl,?_,?_,ready.random,rfl,?_,?_,?_⟩
  · rw [preparationOf_eq C M parameter start resume event next rfl]
    exact path
  · cases write with
    | none => exact ready.memory
    | some symbol =>
        change ParameterInitialisation.BlankMemory M (Function.update source.work source.workHead (some symbol)) origin
          (Function.update target.work target.workHead (some (alphabet M {cell with fixed:=some symbol})))
        dsimp only [cell]
        rw [ready.head]
        exact controller_memory_write C M source.work origin target.work ready.memory source.workHead symbol
  · change Move.stay.onInt target.workHead=0
    rw [ready.head,atOrigin]
    rfl
  · refine ⟨?_,?_,?_⟩
    · change min target.inputHead data.input.length≤data.input.length
      exact Nat.min_le_right _ _
    · change min target.auxiliaryHead data.auxiliary.length≤data.auxiliary.length
      exact Nat.min_le_right _ _
    · change min target.indexHead data.index≤data.index
      exact Nat.min_le_right _ _
  · change min target.inputHead data.input.length=min source.inputHead data.input.length
    rw [ready.input]
  · change min target.auxiliaryHead data.auxiliary.length=min source.auxiliaryHead data.auxiliary.length
    rw [ready.auxiliary]
  · change min target.indexHead data.index=min source.indexHead data.index
    rw [ready.index]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
