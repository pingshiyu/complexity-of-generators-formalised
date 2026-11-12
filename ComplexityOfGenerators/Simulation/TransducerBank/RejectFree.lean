import ComplexityOfGenerators.Simulation.TransducerBank.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

def RejectFree : Prop :=
  ∀ state input auxiliary index origin cell,
    B.transition state input auxiliary index origin cell ≠ .reject

theorem Executes.not_rejected (free : B.RejectFree)
    {data : InputData I A} {bits : BitString} {source : BankConfiguration O Q S k}
    {ticks : ℕ} {result : Outcome O} (execution : B.Executes data bits source ticks result) :
    result ≠ .rejected := by
  induction execution with
  | accept source table => intro impossible; cases impossible
  | reject source table =>
      exact False.elim (free source.state data.input[source.inputHead]?
        data.auxiliary[source.auxiliaryHead]?
        (if source.indexHead < data.index then some () else none)
        (decide (source.head (B.select source.state) = 0))
        (source.tape (B.select source.state) (source.head (B.select source.state))) table)
  | exhausted source no yes table absent => intro impossible; cases impossible
  | random source no yes bit ticks result table lookup rest ih => exact ih
  | step source next write work input auxiliary index emit ticks result table rest ih => exact ih

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
