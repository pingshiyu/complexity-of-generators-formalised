import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Basic

/-! Every ordinary, nonemitting native controller transition is executed in
one physical native step; unbounded source calls are never recompiled. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem controller_next (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
    (source nextSource : Configuration C) (target : Configuration (machine C M parameter start))
    (ready : ControllerReady C M parameter start data origin source target)
    (edge : C.next data bits source=.running nextSource) (noEvent : nextSource.output=source.output) :
    ∃ nextTarget, ControllerReady C M parameter start data origin nextSource nextTarget ∧
      (machine C M parameter start).Steps data bits target 1 nextTarget ∧ nextTarget.output=target.output := by
  cases action : C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead) with
  | accept => simp [Machine.next,action] at edge
  | reject => simp [Machine.next,action] at edge
  | readRandom no yes =>
      cases lookup : bits[source.randomHead]? with
      | none => simp [Machine.next,action,lookup] at edge
      | some bit =>
          simp only [Machine.next,action,lookup,RunState.running.injEq] at edge
          subst nextSource
          let next : Configuration (machine C M parameter start) :=
            {target with
              state:=control C M (.controller (if bit then yes else no))
              randomHead:=target.randomHead+1}
          refine ⟨next,⟨ready.memory,rfl,ready.head,ready.input,ready.auxiliary,ready.index,?_,
            ⟨ready.bounds.input,ready.bounds.auxiliary,ready.bounds.index⟩⟩,?_,rfl⟩
          · change target.randomHead+1=source.randomHead+1
            rw [ready.random]
          · apply Machine.Steps.tail .refl
            have targetTable : (machine C M parameter start).transition target.state data.input[target.inputHead]?
                data.auxiliary[target.auxiliaryHead]? (if target.indexHead<data.index then some () else none)
                (target.work target.workHead)=
                .readRandom (control C M (.controller no)) (control C M (.controller yes)) := by
              rw [ready.state,machine_transition,ready.input,ready.auxiliary,ready.index,ready.head]
              simp only [transition,ready.memory source.workHead,action]
            simp only [Machine.next,targetTable,ready.random,lookup]
            cases bit <;> simp [next,ready.random]
  | step state write work input auxiliary index emit =>
      rw [C.next_step data bits source state write work input auxiliary index emit action] at edge
      cases edge
      have noEmit : emit=none := by
        cases emit with
        | none => rfl
        | some event =>
            have length := congrArg List.length noEvent
            simp only [Machine.stepConfiguration,List.length_append,List.length_singleton] at length
            omega
      subst emit
      let cell := NativeSourceCall.read M (target.work target.workHead)
      let next : Configuration (machine C M parameter start) :=
        (machine C M parameter start).stepConfiguration data target (control C M (.controller state))
          (write.map (fun symbol=>alphabet M {cell with fixed:=some symbol})) work input auxiliary index none
      have targetTable : (machine C M parameter start).transition target.state data.input[target.inputHead]?
          data.auxiliary[target.auxiliaryHead]? (if target.indexHead<data.index then some () else none)
          (target.work target.workHead)=
          .step (control C M (.controller state))
            (write.map (fun symbol=>alphabet M {cell with fixed:=some symbol})) work input auxiliary index none := by
        rw [ready.state,machine_transition,ready.input,ready.auxiliary,ready.index,ready.head]
        simp only [transition,ready.memory source.workHead,action,cell,ready.head]
      refine ⟨next,⟨?_,rfl,?_,?_,?_,?_,ready.random,
        ready.bounds.stepConfiguration C data source _ _ _ _ _ _ _⟩,
        Machine.Steps.tail .refl ((machine C M parameter start).next_step data bits target _ _ _ _ _ _ _ targetTable),rfl⟩
      · cases write with
        | none => exact ready.memory
        | some symbol =>
            change ParameterInitialisation.BlankMemory M (Function.update source.work source.workHead (some symbol)) origin
              (Function.update target.work target.workHead (some (alphabet M {cell with fixed:=some symbol})))
            dsimp only [cell]
            rw [ready.head]
            exact controller_memory_write C M source.work origin target.work ready.memory source.workHead symbol
      · change work.onInt target.workHead=work.onInt source.workHead
        rw [ready.head]
      · change input.onInput data.input.length target.inputHead=input.onInput data.input.length source.inputHead
        rw [ready.input]
      · change auxiliary.onInput data.auxiliary.length target.auxiliaryHead=auxiliary.onInput data.auxiliary.length source.auxiliaryHead
        rw [ready.auxiliary]
      · change index.onInput data.index target.indexHead=index.onInput data.index source.indexHead
        rw [ready.index]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
