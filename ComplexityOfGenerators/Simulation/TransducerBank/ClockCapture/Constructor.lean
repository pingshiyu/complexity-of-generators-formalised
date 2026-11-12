import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.ConstructorStep

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

set_option backward.isDefEq.respectTransparency false

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

 theorem constructor_path (copies n : ℕ) (deterministic : C.Deterministic)
    {start finish : BankConfiguration Unit QC SC kc} {ticks : ℕ}
    (path : C.Steps (decisionData (List.replicate n ())) [] start ticks finish)
    (within : start.inputHead≤n) (bits : BitString) :
    finish.inputHead≤n ∧ ∃ actual, actual≤(copies+2)*ticks ∧
      (bank C B copies).Steps (generatorData n) bits
        (configuration C B copies (.construct start.state)
          (copies*(start.output.length+1)) (copies*(start.output.length+1)) start.inputHead start)
        actual
        (configuration C B copies (.construct finish.state)
          (copies*(finish.output.length+1)) (copies*(finish.output.length+1)) finish.inputHead finish) := by
  induction path with
  | refl start => exact ⟨within,0,by simp,.refl _⟩
  | random start no yes bit ticks finish table lookup rest ih =>
      have never := deterministic start.state
        (List.replicate n ())[start.inputHead]? ([]:List Bool)[start.auxiliaryHead]?
        (if start.indexHead<0 then some () else none)
        (decide (start.head (C.select start.state)=0)) (start.tape (C.select start.state) (start.head (C.select start.state)))
      simp only [TapeBank.instruction,decisionData] at table
      rw [table] at never
      exact False.elim never
  | step start next write work input auxiliary index emit ticks finish table rest ih =>
      have nextWithin : (C.advance (decisionData (List.replicate n ())) start next write work input auxiliary index emit).inputHead≤n := by
        simpa [TapeBank.advance,decisionData] using input.onInput_le n start.inputHead within
      obtain ⟨endWithin,actual,bound,tail⟩ := ih nextWithin
      refine ⟨endWithin,?_⟩
      have first := TapeBank.Steps.single (bank C B copies) (generatorData n) bits
        (configuration C B copies (.construct start.state)
          (copies*(start.output.length+1)) (copies*(start.output.length+1)) start.inputHead start)
        _ _ _ _ _ _ _ (constructor_instruction C B copies _ n start next write work input auxiliary index emit table)
      rw [configuration_constructorStep C B copies _ n start next write work input auxiliary index emit within] at first
      cases emit with
      | none =>
          simp only [Option.isSome_none,Bool.false_eq_true,ite_false] at first
          refine ⟨1+actual,?_,?_⟩
          · simp only [Nat.mul_add,Nat.mul_one]
            omega
          · exact first.trans (bank C B copies) (by simpa [TapeBank.advance] using tail)
      | some unit =>
          cases unit
          have added := write_path C B copies copies (copies*(start.output.length+1))
            (input.onInput n start.inputHead) n (some next)
            (C.advance (decisionData (List.replicate n ())) start next write work input auxiliary index (some ()))
            (by omega) (by simpa [TapeBank.advance,decisionData] using nextWithin) bits
          simp only [Option.isSome_some,ite_true] at first
          simp only [writing,Option.getD_some] at added
          have joined := (first.trans (bank C B copies) (by
            simpa only [TapeBank.advance,decisionData,List.length_replicate] using added)).trans (bank C B copies) (by
            simpa [TapeBank.advance,decisionData,Nat.mul_add,Nat.mul_two,Nat.add_assoc] using tail)
          refine ⟨1+(copies+1)+actual,?_,?_⟩
          · simp only [Nat.mul_add,Nat.mul_one]
            omega
          · simpa [TapeBank.advance,Nat.add_assoc,Nat.mul_add] using joined

end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
