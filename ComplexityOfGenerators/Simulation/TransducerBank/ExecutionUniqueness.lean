import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem Executes.result_unique {data : InputData I A} {bits : BitString}
    {c : BankConfiguration O Q S k} {firstTime secondTime : ℕ} {firstResult secondResult : Outcome O}
    (first : B.Executes data bits c firstTime firstResult)
    (second : B.Executes data bits c secondTime secondResult) : firstResult=secondResult := by
  exact (first.unique B second).2

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
