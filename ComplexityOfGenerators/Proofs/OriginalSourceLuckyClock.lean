import ComplexityOfGenerators.Foundations.ResourceBounds

/-! A single polynomial in final word length bounds the bounded native
controller plus linear original-source work at a polynomially bounded index. -/
namespace ComplexityOfGenerators.OriginalSourceClosure
noncomputable section

def luckyClock (coefficient index work : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial
    (25*(coefficient.asPolynomial.comp index.asPolynomial)^2+(6*index.asPolynomial+20)*work.asPolynomial)

theorem luckyClock_lower (coefficient index work : PolynomialBound) (m : ℕ) :
    25*(coefficient (index m))^2+(6*index m+20)*work m≤luckyClock coefficient index work m := by
  have lower := PolynomialBound.eval_le_ofPolynomial
    (25*(coefficient.asPolynomial.comp index.asPolynomial)^2+(6*index.asPolynomial+20)*work.asPolynomial) m
  change _≤luckyClock coefficient index work m at lower
  simpa only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_comp,
    Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval] using lower

theorem luckyClock_bound (coefficient index work : PolynomialBound) (n m sourceWork : ℕ)
    (small : n ≤ index m) (budget : sourceWork≤work m) :
    25*(coefficient n)^2+(6*n+20)*sourceWork≤luckyClock coefficient index work m := by
  have coefficients : coefficient n≤coefficient (index m) :=
    Nat.mul_le_mul_left coefficient.coefficient (pow_le_pow_left' (by omega) coefficient.degree)
  have squares : (coefficient n)^2≤(coefficient (index m))^2 := by
    simpa only [pow_two] using Nat.mul_le_mul coefficients coefficients
  have factor : 6*n+20≤6*index m+20 := by omega
  exact (Nat.add_le_add (Nat.mul_le_mul_left 25 squares) (Nat.mul_le_mul factor budget)).trans
    (luckyClock_lower coefficient index work m)

end
end ComplexityOfGenerators.OriginalSourceClosure
