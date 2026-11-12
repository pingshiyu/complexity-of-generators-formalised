import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.PathRetry
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Clock

namespace ComplexityOfGenerators.Simulation.ExpectedStarGenerator
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound) (P : BoundedPhaseFamily α)

def workspace : PolynomialBound := PolynomialBound.ofPolynomial
  ((CertifiedStarPhase.cap p).asPolynomial+Polynomial.X*(BoundedMachinePhase.cap P.seed P.clock).asPolynomial)

theorem workspace_lower (n : ℕ) :
    CertifiedStarPhase.cap p n+n*BoundedMachinePhase.cap P.seed P.clock n ≤ workspace p P n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, PolynomialBound.asPolynomial_eval]
  rfl

def primitiveCoefficient : PolynomialBound := PolynomialBound.ofPolynomial
  (100*(Polynomial.X+1)+(FixedBlockRetry.attemptClock (StarCertification.width p)
    (CertifiedStarPhase.cap p) (CertifiedStarPhase.time M p)).asPolynomial+
    2*(ExpectedStarCalls.timeCoefficient P (workspace p P)).asPolynomial+10)

theorem primitiveCoefficient_lower (n : ℕ) :
    100*(n+1)+pathCallBudget M p n+2*ExpectedStarCalls.coefficient P n (workspace p P n)+10 ≤
      primitiveCoefficient M p P n := by
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_one,
    Polynomial.eval_ofNat, PolynomialBound.asPolynomial_eval]
  have outerClock := FixedBlockRetry.attemptBudget_add_two_le (StarCertification.width p)
    (CertifiedStarPhase.cap p) (CertifiedStarPhase.time M p) n
  have innerClock := ExpectedStarCalls.coefficient_le P (workspace p P) n (workspace p P n) le_rfl
  change pathCallBudget M p n ≤ _ at outerClock
  omega

theorem part_le_sum (parts : List ℕ) (j : ℕ) (member : j ∈ parts) : j ≤ parts.sum := by
  induction parts with
  | nil => simp at member
  | cons first parts ih =>
      rcases List.mem_cons.mp member with rfl | member
      · simp only [List.sum_cons]; omega
      · have bound := ih member
        simp only [List.sum_cons]; omega

theorem positive_length_le_sum (parts : List ℕ) (positive : ∀ j ∈ parts, 0 < j) : parts.length ≤ parts.sum := by
  induction parts with
  | nil => simp
  | cons j parts ih =>
      have first := positive j (by simp)
      have tail := ih (fun k member => positive k (by simp [member]))
      simp only [List.length_cons, List.sum_cons]
      omega

end
end ComplexityOfGenerators.Simulation.ExpectedStarGenerator
