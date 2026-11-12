import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Call

/-! A finite seed exhausted by an original source remains genuinely exhausted
in the combined native event machine. No source output is buffered or retried. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem exhausted_event (resume : Fin C.states) (event : E) (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → Fixed C) (length : ℕ) (origin : Bool)
    (unary : ParameterInitialisation.Unary (parameter event) fixed length)
    (c : Configuration (ParameterInitialisation.machine (F:=Fixed C) M (parameter event)))
    (blank : ParameterInitialisation.BlankMemory M fixed origin c.work)
    (initial : c.state=ParameterInitialisation.control .first) (atOrigin : c.workHead=0)
    (bounds : ReadHeadBounds (ParameterInitialisation.machine M (parameter event)) data c)
    (sourceTicks : ℕ) (finishSource : Configuration (selectedSource M start event))
    (sourcePath : (selectedSource M start event).Steps (generatorData length) (bits.drop c.randomHead)
      (selectedSource M start event).initialConfiguration sourceTicks finishSource)
    (exhausted : (selectedSource M start event).observe (generatorData length) (bits.drop c.randomHead) finishSource=.halted .exhausted) :
    ∃ ticks, ticks≤(4*length+16)*(sourceTicks+1) ∧
      (machine C M parameter start).runFrom data bits (prepareConfiguration C M parameter start resume event c) ticks=.halted .exhausted := by
  obtain ⟨prepTicks,prepTime,prepared,preparedState,preparedPath,prepFrame⟩ :=
    ParameterInitialisation.runs M (parameter event) data bits fixed length origin unary c blank initial atOrigin bounds
  have callState := call_prepared C M parameter start event data fixed length prepared preparedState
  have ready := NativeSourceCall.ready_initial (selectedSource M start event) data fixed length
    (callConfiguration C M parameter start event prepared) callState
  have actualSourcePath : (selectedSource M start event).Steps (generatorData length)
      (bits.drop (callConfiguration C M parameter start event prepared).randomHead)
      (selectedSource M start event).initialConfiguration sourceTicks finishSource := by
    simpa only [callConfiguration,prepFrame.random] using sourcePath
  have actualExhausted : (selectedSource M start event).observe (generatorData length)
      (bits.drop (callConfiguration C M parameter start event prepared).randomHead) finishSource=.halted .exhausted := by
    simpa only [callConfiguration,prepFrame.random] using exhausted
  obtain ⟨callClock,callTime,run⟩ := NativeSourceCall.replay_exhausted (selectedSource M start event) data bits fixed length
    (callConfiguration C M parameter start event prepared).randomHead
    (callConfiguration C M parameter start event prepared).output
    (selectedSource M start event).initialConfiguration finishSource
    (callConfiguration C M parameter start event prepared) ready sourceTicks actualSourcePath actualExhausted
  obtain ⟨callTicks,within,finished,callPath,observation⟩ :=
    (NativeSourceCall.machine (F:=Fixed C) (selectedSource M start event)).runFrom_path data bits
      (callConfiguration C M parameter start event prepared) callClock
  have terminal : (NativeSourceCall.machine (F:=Fixed C) (selectedSource M start event)).observe data bits finished=.halted .exhausted :=
    observation.symm.trans run
  have mappedTerminal := RoutineEmbedding.exhausted _ _ _ (source_table C M parameter start resume event)
    data bits finished terminal
  have complete := ((prepare_path C M parameter start resume event data bits preparedPath).trans
    (machine C M parameter start)
    (prepare_handoff C M parameter start resume event data bits prepared preparedState.state preparedState.bounds)).trans
    (machine C M parameter start) (source_path C M parameter start resume event data bits callPath)
  refine ⟨prepTicks+1+callTicks,?_,?_⟩
  · have sourceBound := NativeSourceCall.source_path_bound (selectedSource M start event) length _ sourceTicks finishSource sourcePath
    calc
      prepTicks+1+callTicks ≤ 2*length+2+1+((4*length+12)*sourceTicks+length+1) := by omega
      _ ≤ (4*length+16)*(sourceTicks+1) := by
        simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one]
        omega
  · exact (complete.runFrom (machine C M parameter start)).trans mappedTerminal

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
