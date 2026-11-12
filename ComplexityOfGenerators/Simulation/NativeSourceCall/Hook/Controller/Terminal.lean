import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Basic

/-! The hooked native machine starts from genuinely blank work and finishes
with its physical source output, not its controller's event list. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem initial_controllerReady (data : InputData Unit Bool) :
    ControllerReady C M parameter start data false C.initialConfiguration (machine C M parameter start).initialConfiguration := by
  refine ⟨?_,rfl,rfl,rfl,rfl,rfl,rfl,⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩⟩
  intro position
  simp [ParameterInitialisation.BlankMemory,Machine.initialConfiguration,NativeSourceCall.read]
  rfl

theorem accepting_of_observe (data : InputData Unit Bool) (bits : BitString) (source : Configuration C) (events : List E)
    (accepted : C.observe data bits source=.halted (.accepted events)) :
    C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead)=.accept := by
  cases action : C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead) with
  | accept => rfl
  | reject => simp [Machine.observe,action] at accepted
  | step state write work input auxiliary index emit => simp [Machine.observe,action] at accepted
  | readRandom no yes =>
      simp only [Machine.observe,action] at accepted
      split_ifs at accepted <;> cases accepted

theorem controller_accept (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
    (source : Configuration C) (target : Configuration (machine C M parameter start))
    (ready : ControllerReady C M parameter start data origin source target)
    (action : C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead)=.accept) :
    (machine C M parameter start).observe data bits target=.halted (.accepted target.output) := by
  have table : (machine C M parameter start).transition target.state data.input[target.inputHead]?
      data.auxiliary[target.auxiliaryHead]? (if target.indexHead<data.index then some () else none) (target.work target.workHead)=.accept := by
    rw [ready.state,machine_transition,ready.input,ready.auxiliary,ready.index,ready.head]
    simp only [transition,ready.memory source.workHead,action]
  simp only [Machine.observe,table]

theorem controller_exhausted (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
    (source : Configuration C) (target : Configuration (machine C M parameter start))
    (ready : ControllerReady C M parameter start data origin source target)
    (no yes : Fin C.states)
    (action : C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead)=.readRandom no yes)
    (absent : bits[source.randomHead]?=none) :
    (machine C M parameter start).observe data bits target=.halted .exhausted := by
  have table : (machine C M parameter start).transition target.state data.input[target.inputHead]?
      data.auxiliary[target.auxiliaryHead]? (if target.indexHead<data.index then some () else none) (target.work target.workHead)=
      .readRandom (control C M (.controller no)) (control C M (.controller yes)) := by
    rw [ready.state,machine_transition,ready.input,ready.auxiliary,ready.index,ready.head]
    simp only [transition,ready.memory source.workHead,action]
  have missing : ¬target.randomHead<bits.length := by
    rw [ready.random]
    exact Nat.not_lt_of_ge (List.getElem?_eq_none_iff.mp absent)
  simp only [Machine.observe,table,missing,↓reduceIte]

theorem controller_exhausted_of_observe (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
    (source : Configuration C) (target : Configuration (machine C M parameter start))
    (ready : ControllerReady C M parameter start data origin source target)
    (terminal : C.observe data bits source=.halted .exhausted) :
    (machine C M parameter start).observe data bits target=.halted .exhausted := by
  cases action : C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead) with
  | accept => simp [Machine.observe,action] at terminal
  | reject => simp [Machine.observe,action] at terminal
  | step state write work input auxiliary index emit => simp [Machine.observe,action] at terminal
  | readRandom no yes =>
      cases lookup : bits[source.randomHead]? with
      | none => exact controller_exhausted C M parameter start data bits origin source target ready no yes action lookup
      | some bit =>
          have available := (List.getElem?_eq_some_iff.mp lookup).1
          simp [Machine.observe,action,available] at terminal

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
