import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Write

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

 theorem unary_input (n p : ℕ) : (List.replicate n ())[p]? = if p<n then some () else none := by
  simp [List.getElem?_replicate]

 theorem constructor_instruction (copies fuel n : ℕ) (ctor : BankConfiguration Unit QC SC kc)
    (next write work input auxiliary index emit)
    (table : C.instruction (decisionData (List.replicate n ())) ctor =
      .step next write work input auxiliary index emit) :
    (bank C B copies).instruction (generatorData n)
      (configuration C B copies (.construct ctor.state) fuel fuel ctor.inputHead ctor) =
      .step (if emit.isSome then .append next ⟨copies,by omega⟩ else .construct next)
        (write,.inl B.blank) work .stay .stay input none := by
  simp only [TapeBank.instruction,decisionData,List.getElem?_nil,Nat.not_lt_zero,ite_false,
    unary_input] at table
  simp only [TapeBank.instruction,configuration,bank,generatorData,Fin.addCases_left]
  rw [show C.transition ctor.state (if ctor.inputHead<n then some () else none) none none
    (decide (ctor.head (C.select ctor.state)=0)) (ctor.tape (C.select ctor.state) (ctor.head (C.select ctor.state))) =
      .step next write work input auxiliary index emit from table]

 theorem configuration_constructorStep (copies fuel n : ℕ)
    (ctor : BankConfiguration Unit QC SC kc) (next write work input auxiliary index emit)
    (within : ctor.inputHead≤n) :
    (bank C B copies).advance (generatorData n)
      (configuration C B copies (.construct ctor.state) fuel fuel ctor.inputHead ctor)
      (if emit.isSome then .append next ⟨copies,by omega⟩ else .construct next)
      (write,.inl B.blank) work .stay .stay input none =
      configuration C B copies
        (if emit.isSome then .append next ⟨copies,by omega⟩ else .construct next) fuel fuel
        ((C.advance (decisionData (List.replicate n ())) ctor next write work input auxiliary index emit).inputHead)
        (C.advance (decisionData (List.replicate n ())) ctor next write work input auxiliary index emit) := by
  apply BankConfiguration.ext <;> try rfl
  case indexHead => simp [TapeBank.advance,configuration,generatorData,decisionData]
  case head =>
    simp only [TapeBank.advance,configuration,bank,Fin.addCases_left,BankEmbedding.update_left]
  case tape =>
    simp only [TapeBank.advance,configuration,bank,Fin.addCases_left,BankEmbedding.update_left]
    congr 1
    funext j p
    by_cases same : j=C.select ctor.state
    · subst j
      by_cases position : p=ctor.head (C.select ctor.state)
      · subst p; simp
      · simp [Function.update_of_ne position]
    · simp [Function.update_of_ne same]

 theorem constructor_accept_instruction (copies fuel n : ℕ) (ctor : BankConfiguration Unit QC SC kc)
    (table : C.instruction (decisionData (List.replicate n ())) ctor = .accept) :
    (bank C B copies).instruction (generatorData n)
      (configuration C B copies (.construct ctor.state) fuel fuel ctor.inputHead ctor) =
      .step .rewind (ctor.tape (C.select ctor.state) (ctor.head (C.select ctor.state)),.inl B.blank)
        .stay .stay .stay .stay none := by
  simp only [TapeBank.instruction,decisionData,List.getElem?_nil,Nat.not_lt_zero,ite_false,
    unary_input] at table
  simp only [TapeBank.instruction,configuration,bank,generatorData,Fin.addCases_left]
  rw [show C.transition ctor.state (if ctor.inputHead<n then some () else none) none none
    (decide (ctor.head (C.select ctor.state)=0)) (ctor.tape (C.select ctor.state) (ctor.head (C.select ctor.state))) =
      .accept from table]

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
