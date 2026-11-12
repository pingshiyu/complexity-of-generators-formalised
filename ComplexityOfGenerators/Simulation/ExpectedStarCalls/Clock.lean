import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Execution
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Clock

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

/-- A polynomial ceiling for one attempted source call, including collection
and loop control. The source machine appears only in its fixed clock. -/
def callClock : PolynomialBound := FixedBlockRetry.attemptClock P.seed
  (BoundedMachinePhase.cap P.seed P.clock) (BoundedMachinePhase.time P.machine P.seed P.clock)

theorem callBudget_le (n : ℕ) : callBudget P n ≤ callClock P n :=
  FixedBlockRetry.attemptBudget_add_two_le _ _ _ n

/-- The outer workspace can be any polynomial already established for the
certification prefix and all buffered factor outputs. -/
def timeCoefficient (workspace : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  ((callClock P).asPolynomial+1000*(workspace.asPolynomial+(BoundedMachinePhase.cap P.seed P.clock).asPolynomial+1)+10)

theorem coefficient_le (workspace : PolynomialBound) (n ceiling : ℕ) (fits : ceiling ≤ workspace n) :
    coefficient P n ceiling ≤ timeCoefficient P workspace n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_one, Polynomial.eval_ofNat,
    PolynomialBound.asPolynomial_eval]
  have clock := callBudget_le P n
  unfold coefficient
  omega

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
