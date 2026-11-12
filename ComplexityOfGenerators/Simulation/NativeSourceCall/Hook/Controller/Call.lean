import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Event
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Call
import ComplexityOfGenerators.Foundations.RandomCursorRebase

/-! A source-call event returns a concrete controller snapshot with its random
cursor advanced by exactly the original source's consumed prefix. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem controller_event_accepted (data : InputData Unit Bool) (bits : BitString) (origin : Bool)
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
    (word : List O) (accepted : (selectedSource M start event).observe (generatorData length) (bits.drop source.randomHead) finishSource=.halted (.accepted word)) :
    ∃ ticks finishTarget, ticks≤1+(6*length+20)*(sourceTicks+1) ∧
      ControllerReady C M parameter start data true
        (C.rebaseRandom (C.stepConfiguration data source resume write .stay .stay .stay .stay (some event))
          (source.randomHead+finishSource.randomHead)) finishTarget ∧
      (machine C M parameter start).Steps data bits target ticks finishTarget ∧ finishTarget.output=target.output++word := by
  obtain ⟨prepared,eventPath,blank,initial,head,bounds,random,output,input,auxiliary,index⟩ :=
    event_step C M parameter start data bits origin source target ready resume write event atOrigin action
  have actualSourcePath : (selectedSource M start event).Steps (generatorData length) (bits.drop prepared.randomHead)
      (selectedSource M start event).initialConfiguration sourceTicks finishSource := by simpa only [random] using sourcePath
  have actualAccepted : (selectedSource M start event).observe (generatorData length) (bits.drop prepared.randomHead) finishSource=.halted (.accepted word) := by
    simpa only [random] using accepted
  obtain ⟨callTicks,finish,callTime,state,finishHead,clean,callPath,finishRandom,finishOutput,finishInput,finishAuxiliary,finishIndex⟩ :=
    accepted_event C M parameter start resume event data bits
      (C.stepConfiguration data source resume write .stay .stay .stay .stay (some event)).work length origin unary
      prepared blank initial head bounds sourceTicks finishSource actualSourcePath word actualAccepted
  refine ⟨1+callTicks,finish,Nat.add_le_add_left callTime _,?_,eventPath.trans (machine C M parameter start) callPath,?_⟩
  · refine ⟨clean,state,?_,finishInput.trans input,finishAuxiliary.trans auxiliary,finishIndex.trans index,?_,?_⟩
    · change finish.workHead=Move.stay.onInt source.workHead
      rw [finishHead,atOrigin]
      rfl
    · change finish.randomHead=source.randomHead+finishSource.randomHead
      simpa only [random] using finishRandom
    · have actualBounds := ready.bounds.stepConfiguration C data source resume write .stay .stay .stay .stay (some event)
      exact ⟨actualBounds.input,actualBounds.auxiliary,actualBounds.index⟩
  · simpa only [output] using finishOutput

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
