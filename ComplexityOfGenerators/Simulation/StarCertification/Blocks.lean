import ComplexityOfGenerators.Simulation.StarCertification.Model
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

namespace ComplexityOfGenerators.Simulation.StarCertification
set_option backward.isDefEq.respectTransparency true
noncomputable section

theorem used_bound (p : PolynomialBound) (start count : ℕ) :
    used p start count ≤ count*IndexwiseCertification.seed p (start+count) := by
  induction count generalizing start with
  | zero => simp [used]
  | succ count ih =>
      have next := ih (start+1)
      have same : start+1+count = start+(count+1) := by omega
      rw [same] at next
      have first := (IndexwiseCertification.seed p).monotone (by omega : start+1 ≤ start+(count+1))
      simp only [used]
      nlinarith

/-- Enough fixed coins for every bounded test and a subsequent n-1-cut
composition proposal. The extra summand also makes zero's block positive. -/
noncomputable def width (p : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  ((Polynomial.X+1)*((IndexwiseCertification.seed p).asPolynomial+1))

theorem width_lower (p : PolynomialBound) (n : ℕ) :
    (n+1)*(IndexwiseCertification.seed p n+1) ≤ width p n := by
  unfold width
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_one,
    Polynomial.eval_ofNat,Polynomial.eval_C,PolynomialBound.asPolynomial_eval]
  rfl

private theorem width_tests_plus (p : PolynomialBound) (n : ℕ) : used p 0 n+n ≤ width p n := by
  have bound := used_bound p 0 n
  simp only [Nat.zero_add] at bound
  calc
    used p 0 n+n ≤ n*IndexwiseCertification.seed p n+n := Nat.add_le_add_right bound n
    _ ≤ (n+1)*(IndexwiseCertification.seed p n+1) := by nlinarith
    _ ≤ width p n := width_lower p n

theorem width_tests (p : PolynomialBound) (n : ℕ) : used p 0 n+n-1 ≤ width p n :=
  (Nat.sub_le _ _).trans (width_tests_plus p n)

theorem width_remaining (p : PolynomialBound) (n : ℕ) : n-1 ≤ width p n-used p 0 n := by
  have enough := width_tests_plus p n
  omega

end
end ComplexityOfGenerators.Simulation.StarCertification
