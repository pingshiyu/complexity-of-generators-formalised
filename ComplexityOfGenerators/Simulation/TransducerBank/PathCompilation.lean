import ComplexityOfGenerators.Simulation.TransducerBank.Execution

/-! Open finite bank paths compile from an arbitrary genuine native snapshot;
terminal observation is not required at the endpoint. -/
namespace ComplexityOfGenerators.Simulation.TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
    [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

theorem bank_steps_path {data : InputData I A} {bits : BitString}
    {source finish : BankConfiguration O Q S k} {t : ℕ} (path : B.Steps data bits source t finish)
    (r : ℕ) (negative : Fin k→Bool) (start : Configuration (bankMachine B))
    (ready : BankReady B source negative start) (bounded : B.Bounded data r source) :
    ∃ ticks next sides, BankReady B finish sides next ∧ (bankMachine B).Steps data bits start ticks next := by
  induction path generalizing r negative start with
  | refl source => exact ⟨0,start,negative,ready,.refl⟩
  | random source no yes bit t finish table lookup rest ih =>
      obtain ⟨s,middle,_,middleReady,first,_⟩ :=
        bank_random_path B data bits r source negative start ready bounded no yes bit table lookup
      obtain ⟨u,next,sides,nextReady,tail⟩ := ih (r+1) negative middle middleReady
        (B.choose_bounded data r source _ bounded)
      exact ⟨s+u,next,sides,nextReady,first.trans (bankMachine B) tail⟩
  | step source next write work input auxiliary index emit t finish table rest ih =>
      obtain ⟨s,middle,middleSides,_,middleReady,first,_⟩ :=
        bank_step_path B data bits r source negative start ready bounded next write work input auxiliary index emit table
      obtain ⟨u,target,sides,targetReady,tail⟩ := ih (r+1) middleSides middle middleReady
        (B.advance_bounded data r source next write work input auxiliary index emit bounded)
      exact ⟨s+u,target,sides,targetReady,first.trans (bankMachine B) tail⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank
