import ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation.First

/-! A prepared packet is obtained by real writes and a real rewind, with
linear cost even when the caller's fixed track has unbounded ambient support. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O]
    (M : Machine Unit Bool O) (parameter : F → Bool)

theorem runs (data : InputData Unit Bool) (bits : BitString) (fixed : ℤ → F)
    (length : ℕ) (origin : Bool) (unary : Unary parameter fixed length)
    (c : Configuration (machine M parameter))
    (blank : BlankMemory M fixed origin c.work) (initial : c.state=control .first)
    (atOrigin : c.workHead=0) (bounds : ReadHeadBounds (machine M parameter) data c) :
    ∃ ticks≤2*length+2, ∃ d,
      State M parameter data fixed {0} (packet length 0 0) .done 0 d ∧
      (machine M parameter).Steps data bits c ticks d ∧ WorkFrame (machine M parameter) c d := by
  obtain ⟨middle,firstState,first,firstFrame⟩ :=
    first_step M parameter data bits fixed length origin unary c blank initial atOrigin bounds
  cases length with
  | zero =>
      refine ⟨1,by omega,middle,?_,first,firstFrame⟩
      simpa [←packetPrefix_complete 0] using firstState
  | succ size =>
      have scanState : State M parameter data fixed {0} (packetPrefix (size+1) 1) .scan 1 middle := by
        simpa using firstState
      obtain ⟨last,lastState,scanPath,scanFrame⟩ := scan M parameter data bits fixed (size+1)
        size 1 (by omega) (by omega) unary middle scanState
      obtain ⟨d,result,rewindPath,rewindFrame⟩ := rewind M parameter data bits fixed (size+1)
        (size+1) last lastState
      refine ⟨1+(size+1)+(size+1+1),by omega,d,result,?_,?_⟩
      · exact Machine.Steps.trans (machine M parameter)
          (Machine.Steps.trans (machine M parameter) first scanPath) rewindPath
      · exact WorkFrame.trans (machine M parameter)
          (WorkFrame.trans (machine M parameter) firstFrame scanFrame) rewindFrame

/-- Preparation accepts without consuming a random bit or emitting a symbol.
The endpoint specification is also available separately through `runs` for a
caller that transfers control directly into the source routine. -/
theorem runFrom_accepts (data : InputData Unit Bool) (bits : BitString) (fixed : ℤ → F)
    (length : ℕ) (origin : Bool) (unary : Unary parameter fixed length)
    (c : Configuration (machine M parameter))
    (blank : BlankMemory M fixed origin c.work) (initial : c.state=control .first)
    (atOrigin : c.workHead=0) (bounds : ReadHeadBounds (machine M parameter) data c) :
    ∃ ticks≤2*length+2,
      (machine M parameter).runFrom data bits c ticks = .halted (.accepted c.output) := by
  obtain ⟨ticks,bound,d,result,path,frame⟩ :=
    runs M parameter data bits fixed length origin unary c blank initial atOrigin bounds
  refine ⟨ticks,bound,?_⟩
  rw [path.runFrom (machine M parameter)]
  simp [Machine.observe,result.state,machine_transition,transition,frame.output]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.ParameterInitialisation
