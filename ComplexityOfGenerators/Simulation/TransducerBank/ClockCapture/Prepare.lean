import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Rewind

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

/-- The physical clock and a fresh source bank are reached from genuinely
blank tapes, charging capture and both head resets. -/
 theorem prepare_path (copies n time ctorTicks : ℕ) (positive : 1≤copies) (dominates : n≤time)
    (deterministic : C.Deterministic)
    (constructor : C.Executes (decisionData (List.replicate n ())) [] C.initialConfiguration
      ctorTicks (.accepted (List.replicate time ()))) (bits : BitString) :
    ∃ ticks ctor, ticks≤(copies+1)+(copies+2)*ctorTicks+1+(copies*(time+1)+1) ∧
      (bank C B copies).Steps (generatorData n) bits (bank C B copies).initialConfiguration ticks
        (configuration C B copies (.source (.fetch B.initial)) (copies*(time+1)) 0 0 ctor) := by
  obtain ⟨ctor,path,halt⟩ := constructor.path C
  have terminal : C.instruction (decisionData (List.replicate n ())) ctor=.accept ∧
      ctor.output=List.replicate time () := by
    generalize outcome : Outcome.accepted (List.replicate time ())=result at halt
    cases halt with
    | accept ctor table => exact ⟨table,(Outcome.accepted.inj outcome).symm⟩
    | reject => cases outcome
    | exhausted => cases outcome
  obtain ⟨table,output⟩ := terminal
  obtain ⟨within,ticks,cost,simulation⟩ := constructor_path C B copies n deterministic path
    (by simp [TapeBank.initialConfiguration]) bits
  have leading := write_path C B copies copies 0 0 n none C.initialConfiguration (by omega) (by omega) bits
  have acceptance := TapeBank.Steps.single (bank C B copies) (generatorData n) bits
    (configuration C B copies (.construct ctor.state) (copies*(time+1)) (copies*(time+1)) ctor.inputHead ctor)
    .rewind (ctor.tape (C.select ctor.state) (ctor.head (C.select ctor.state)),.inl B.blank)
    .stay .stay .stay .stay none (constructor_accept_instruction C B copies _ n ctor table)
  have cell : (ctor.tape (C.select ctor.state) (ctor.head (C.select ctor.state)),.inl B.blank) =
      (configuration C B copies (.construct ctor.state) (copies*(time+1)) (copies*(time+1)) ctor.inputHead ctor).tape
        ((bank C B copies).select (.construct ctor.state))
        ((configuration C B copies (.construct ctor.state) (copies*(time+1)) (copies*(time+1)) ctor.inputHead ctor).head
          ((bank C B copies).select (.construct ctor.state))) := by
    simp only [configuration,bank,Fin.addCases_left]
  rw [cell,configuration_stay C B copies _ _ _ n _ _ ctor within] at acceptance
  have reset := rewind_path C B copies (copies*(time+1)) (copies*(time+1)) ctor.inputHead n ctor within bits
  have resetIndex : ctor.inputHead-copies*(time+1)=0 := by
    have lower : time+1≤copies*(time+1) := Nat.le_mul_of_pos_left _ (by omega)
    omega
  rw [resetIndex] at reset
  have leading' : (bank C B copies).Steps (generatorData n) bits (bank C B copies).initialConfiguration
      (copies+1) (configuration C B copies (.construct C.initial) copies copies 0 C.initialConfiguration) := by
    simpa [writing,initial_configuration] using leading
  have simulation' : (bank C B copies).Steps (generatorData n) bits
      (configuration C B copies (.construct C.initial) copies copies 0 C.initialConfiguration) ticks
      (configuration C B copies (.construct ctor.state) (copies*(time+1)) (copies*(time+1)) ctor.inputHead ctor) := by
    simpa [TapeBank.initialConfiguration,output] using simulation
  refine ⟨(copies+1)+ticks+1+(copies*(time+1)+1),ctor,by omega,?_⟩
  exact ((leading'.trans (bank C B copies) simulation').trans (bank C B copies) acceptance).trans (bank C B copies) reset

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
