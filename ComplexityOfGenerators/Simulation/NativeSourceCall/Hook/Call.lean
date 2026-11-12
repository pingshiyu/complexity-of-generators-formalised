import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Transfers
import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.Execution
import ComplexityOfGenerators.Simulation.NativeSourceCall.Execution

/-! A complete native event call: actual fixed-track unary preparation, original
source execution, linear cleanup, and resumption of the suspended controller.
The bound uses only original source elapsed time, never its square. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem accepted_event (resume : Fin C.states) (event : E) (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → Fixed C) (length : ℕ) (origin : Bool)
    (unary : ParameterInitialisation.Unary (parameter event) fixed length)
    (c : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event)))
    (blank : ParameterInitialisation.BlankMemory M fixed origin c.work)
    (initial : c.state=ParameterInitialisation.control .first) (atOrigin : c.workHead=0)
    (bounds : ReadHeadBounds (ParameterInitialisation.machine M (parameter event)) data c)
    (sourceTicks : ℕ) (finishSource : Configuration (selectedSource M start event))
    (sourcePath : (selectedSource M start event).Steps (generatorData length) (bits.drop c.randomHead)
      (selectedSource M start event).initialConfiguration sourceTicks finishSource)
    (word : List O) (accepted : (selectedSource M start event).observe (generatorData length) (bits.drop c.randomHead) finishSource=.halted (.accepted word)) :
    ∃ ticks finishTarget, ticks≤(6*length+20)*(sourceTicks+1) ∧
      finishTarget.state=control C M (.controller resume) ∧ finishTarget.workHead=0 ∧
      ParameterInitialisation.BlankMemory M fixed true finishTarget.work ∧
      (machine C M parameter start).Steps data bits (prepareConfiguration C M parameter start resume event c) ticks finishTarget ∧
      finishTarget.randomHead=c.randomHead+finishSource.randomHead ∧ finishTarget.output=c.output++word ∧
      finishTarget.inputHead=c.inputHead ∧ finishTarget.auxiliaryHead=c.auxiliaryHead ∧ finishTarget.indexHead=c.indexHead := by
  obtain ⟨prepTicks,prepTime,prepared,preparedState,preparedPath,prepFrame⟩ :=
    ParameterInitialisation.runs M (parameter event) data bits fixed length origin unary c blank initial atOrigin bounds
  have callState := call_prepared C M parameter start event data fixed length prepared preparedState
  have actualSourcePath : (selectedSource M start event).Steps (generatorData length)
      (bits.drop (callConfiguration C M parameter start event prepared).randomHead)
      (selectedSource M start event).initialConfiguration sourceTicks finishSource := by
    simpa only [callConfiguration,prepFrame.random] using sourcePath
  have actualAccepted : (selectedSource M start event).observe (generatorData length)
      (bits.drop (callConfiguration C M parameter start event prepared).randomHead) finishSource=.halted (.accepted word) := by
    simpa only [callConfiguration,prepFrame.random] using accepted
  obtain ⟨callTicks,finished,callTime,doneState,callPath,random,output,input,auxiliary,index⟩ :=
    NativeSourceCall.accepted_call (selectedSource M start event) data bits fixed length
      (callConfiguration C M parameter start event prepared) callState sourceTicks finishSource actualSourcePath word actualAccepted
  let finish := resumedConfiguration C M parameter start resume event finished
  have handoff := prepare_handoff C M parameter start resume event data bits prepared preparedState.state preparedState.bounds
  have complete := (((prepare_path C M parameter start resume event data bits preparedPath).trans
    (machine C M parameter start) handoff).trans (machine C M parameter start)
    (source_path C M parameter start resume event data bits callPath)).trans (machine C M parameter start)
    (source_handoff C M parameter start resume event data bits finished doneState.state doneState.bounds)
  refine ⟨prepTicks+1+callTicks+1,finish,?_,rfl,doneState.head,?_,complete,?_,?_,?_,?_,?_⟩
  · have extra : 2*length+4≤(2*length+4)*(sourceTicks+1) := by
      simpa only [Nat.mul_one] using Nat.mul_le_mul_left (2*length+4) (Nat.succ_le_succ (Nat.zero_le sourceTicks))
    calc
      prepTicks+1+callTicks+1 ≤ (4*length+16)*(sourceTicks+1)+(2*length+4) := by omega
      _ ≤ (4*length+16)*(sourceTicks+1)+(2*length+4)*(sourceTicks+1) := Nat.add_le_add_left extra _
      _ = (6*length+20)*(sourceTicks+1) := by
        rw [←Nat.add_mul]
        congr 1
        omega
  · intro position
    change NativeSourceCall.read M (finished.work position)=_
    have represented := doneState.memory position
    rw [selected_read] at represented
    simpa using represented
  · change finished.randomHead=c.randomHead+finishSource.randomHead
    simpa only [callConfiguration,prepFrame.random] using random
  · change finished.output=c.output++word
    simpa only [callConfiguration,prepFrame.output] using output
  · change finished.inputHead=c.inputHead
    exact input.trans prepFrame.input
  · change finished.auxiliaryHead=c.auxiliaryHead
    exact auxiliary.trans prepFrame.auxiliary
  · change finished.indexHead=c.indexHead
    exact index.trans prepFrame.index

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
