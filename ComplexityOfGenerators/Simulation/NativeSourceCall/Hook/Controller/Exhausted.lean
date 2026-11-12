import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Event
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.ExhaustedCall

namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem controller_event_exhausted (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
    (source : Configuration C) (target : Configuration (machine C M parameter start))
    (ready : ControllerReady C M parameter start data origin source target)
    (resume : Fin C.states) (write : Option (Fin C.symbols)) (event : E) (length : ℕ)
    (atOrigin : source.workHead=0)
    (action : C.transition source.state data.input[source.inputHead]? data.auxiliary[source.auxiliaryHead]?
      (if source.indexHead<data.index then some () else none) (source.work source.workHead)=
      .step resume write .stay .stay .stay .stay (some event))
    (unary : ParameterInitialisation.Unary (parameter event)
      (C.stepConfiguration data source resume write .stay .stay .stay .stay (some event)).work length)
    (sourceTicks : ℕ) (finishSource : Configuration (selectedSource M start event))
    (sourcePath : (selectedSource M start event).Steps (generatorData length) (bits.drop source.randomHead)
      (selectedSource M start event).initialConfiguration sourceTicks finishSource)
    (exhausted : (selectedSource M start event).observe (generatorData length) (bits.drop source.randomHead) finishSource=.halted .exhausted) :
    ∃ ticks, ticks≤1+(4*length+16)*(sourceTicks+1) ∧
      (machine C M parameter start).runFrom data bits target ticks=.halted .exhausted := by
  obtain ⟨prepared,eventPath,blank,initial,head,bounds,random,output,input,auxiliary,index⟩ :=
    event_step C M parameter start data bits origin source target ready resume write event atOrigin action
  have actualSourcePath : (selectedSource M start event).Steps (generatorData length) (bits.drop prepared.randomHead)
      (selectedSource M start event).initialConfiguration sourceTicks finishSource := by simpa only [random] using sourcePath
  have actualExhausted : (selectedSource M start event).observe (generatorData length) (bits.drop prepared.randomHead) finishSource=.halted .exhausted := by
    simpa only [random] using exhausted
  obtain ⟨callTicks,callTime,run⟩ := exhausted_event C M parameter start resume event data bits
    (C.stepConfiguration data source resume write .stay .stay .stay .stay (some event)).work length origin unary
    prepared blank initial head bounds sourceTicks finishSource actualSourcePath actualExhausted
  refine ⟨1+callTicks,Nat.add_le_add_left callTime _,?_⟩
  rw [(machine C M parameter start).runFrom_add data bits target _ 1 (eventPath.runFrom (machine C M parameter start)),run]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
