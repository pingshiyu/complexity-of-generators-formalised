import ComplexityOfGenerators.Simulation.FixedBlockRetry.State
import ComplexityOfGenerators.Foundations.ResourceBounds

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
noncomputable section

/-- A common polynomial bound for one complete attempted block, including
collection, phase execution, restoration and the enclosing loop transfers. -/
def attemptClock (width cap time : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  (52*cap.asPolynomial+12*width.asPolynomial+(WordStack.Command.counterBudget width).asPolynomial+time.asPolynomial+27)

theorem attemptBudget_add_two_le (width cap time : PolynomialBound) (n : ℕ) :
    attemptBudget width cap time n+2 ≤ attemptClock width cap time n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat, PolynomialBound.asPolynomial_eval]
  unfold attemptBudget collectBudget
  omega

end
end ComplexityOfGenerators.Simulation.FixedBlockRetry
