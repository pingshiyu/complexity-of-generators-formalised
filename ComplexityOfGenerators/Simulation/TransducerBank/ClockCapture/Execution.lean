import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Source

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

 theorem bounded_execution (copies n time ctorTicks : ℕ) (positive : 1≤copies) (dominates : n≤time)
    (deterministic : C.Deterministic)
    (constructor : C.Executes (decisionData (List.replicate n ())) [] C.initialConfiguration
      ctorTicks (.accepted (List.replicate time ()))) (bits : BitString) :
    ∃ ticks result,
      ticks≤(copies+1)+(copies+2)*ctorTicks+1+(copies*(time+1)+1)+(3*(copies*(time+1))+1) ∧
      (bank C B copies).Executes (generatorData n) bits (bank C B copies).initialConfiguration ticks result ∧
      (∀ word,result=.accepted word → ∃ sourceTicks,sourceTicks≤copies*(time+1) ∧
        B.Executes (generatorData n) bits B.initialConfiguration sourceTicks (.accepted word)) := by
  obtain ⟨before,ctor,charge,preparation⟩ :=
    prepare_path C B copies n time ctorTicks positive dominates deterministic constructor bits
  obtain ⟨after,result,bound,execution,sound⟩ := Fuel.bounded_execution B (generatorData n) bits
    (copies*(time+1)) (copies*(time+1)) 0 0 B.initialConfiguration (B.initial_bounded _) (by omega)
  have lifted := source_executes C B copies ctor.head (fun j p=>(ctor.tape j p,.inl B.blank)) execution
  rw [←source_configuration C B copies (copies*(time+1)) ctor] at lifted
  refine ⟨before+after,result,by omega,preparation.executes (bank C B copies) lifted,?_⟩
  exact sound

 theorem accepted_executes (copies n time ctorTicks : ℕ) (positive : 1≤copies) (dominates : n≤time)
    (deterministic : C.Deterministic)
    (constructor : C.Executes (decisionData (List.replicate n ())) [] C.initialConfiguration
      ctorTicks (.accepted (List.replicate time ())))
    (bits : BitString) (sourceTicks : ℕ) (word : List O)
    (capacity : sourceTicks≤copies*(time+1))
    (source : B.Executes (generatorData n) bits B.initialConfiguration sourceTicks (.accepted word)) :
    ∃ ticks, (bank C B copies).Executes (generatorData n) bits (bank C B copies).initialConfiguration ticks (.accepted word) := by
  obtain ⟨before,ctor,charge,preparation⟩ :=
    prepare_path C B copies n time ctorTicks positive dominates deterministic constructor bits
  have execution := Fuel.accepted_executes B (generatorData n) bits (copies*(time+1)) sourceTicks 0 0
    B.initialConfiguration word (B.initial_bounded _) source (by omega)
  have lifted := source_executes C B copies ctor.head (fun j p=>(ctor.tape j p,.inl B.blank)) execution
  rw [←source_configuration C B copies (copies*(time+1)) ctor] at lifted
  exact ⟨before+3*sourceTicks,preparation.executes (bank C B copies) lifted⟩

 theorem accepted_iff (copies n time ctorTicks : ℕ) (positive : 1≤copies) (dominates : n≤time)
    (deterministic : C.Deterministic)
    (constructor : C.Executes (decisionData (List.replicate n ())) [] C.initialConfiguration
      ctorTicks (.accepted (List.replicate time ()))) (bits : BitString) (word : List O) :
    (∃ ticks,(bank C B copies).Executes (generatorData n) bits (bank C B copies).initialConfiguration ticks (.accepted word)) ↔
      ∃ ticks,ticks≤copies*(time+1) ∧ B.Executes (generatorData n) bits B.initialConfiguration ticks (.accepted word) := by
  constructor
  · rintro ⟨ticks,execution⟩
    obtain ⟨other,result,charge,run,sound⟩ :=
      bounded_execution C B copies n time ctorTicks positive dominates deterministic constructor bits
    exact sound word (TapeBank.Executes.unique (bank C B copies) run execution).2
  · rintro ⟨ticks,capacity,source⟩
    exact accepted_executes C B copies n time ctorTicks positive dominates deterministic constructor bits ticks word capacity source

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
