import ComplexityOfGenerators.Simulation.TransducerBank.Basic

/-! Determinism after fixing the explicit finite choice tape. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem Executes.unique {data : InputData I A} {bits : BitString}
    {source : BankConfiguration O Q S k} {ticks otherTicks : ℕ} {result otherResult : Outcome O}
    (first : B.Executes data bits source ticks result)
    (second : B.Executes data bits source otherTicks otherResult) :
    ticks = otherTicks ∧ result = otherResult := by
  induction first generalizing otherTicks otherResult with
  | accept source table => cases second <;> simp_all
  | reject source table => cases second <;> simp_all
  | exhausted source no yes table absent => cases second <;> simp_all
  | random source no yes bit ticks result table lookup rest ih =>
      cases second <;> simp_all
      exact ih ‹_›
  | step source next write work input auxiliary index emit ticks result table rest ih =>
      cases second <;> simp_all
      exact ih ‹_›

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
