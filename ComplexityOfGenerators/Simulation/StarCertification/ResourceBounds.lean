import ComplexityOfGenerators.Simulation.StarCertification.Bounds

namespace ComplexityOfGenerators.Simulation.StarCertification
open WordStack
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
noncomputable section

/-- A polynomial workspace accommodates the supplied caller data and each
bounded source snapshot, uniformly over all tested indices at most n. -/
noncomputable def workspace (p initial : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  (initial.asPolynomial+Polynomial.X+(IndexwiseCertification.seed p).asPolynomial+
    3*((IndexwiseCertification.clock p).asPolynomial+1)+10)

theorem workspace_lower (p initial : PolynomialBound) (n : ℕ) :
    initial n+n+IndexwiseCertification.seed p n+3*(IndexwiseCertification.clock p n+1)+10 ≤ workspace p initial n := by
  unfold workspace
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,
    Polynomial.eval_one,PolynomialBound.asPolynomial_eval]
  rfl

noncomputable def nativeConstant : ℕ :=
  (Source.body M (encode M) (decode M) (Source.bank BoundedSource.sourceSlots)).bound+500

/-- An explicit polynomial for the actual finite native certification scan.
Its source calls are capped; no unproved runtime-distribution assumption enters
this resource bound. -/
noncomputable def primitiveTime (p initial : PolynomialBound) : PolynomialBound := PolynomialBound.ofPolynomial
  (Polynomial.X*(Polynomial.C (nativeConstant M)*((workspace p initial).asPolynomial+1)+
    (Command.counterBudget (IndexwiseCertification.seed p)).asPolynomial+
    (Command.counterBudget (IndexwiseCertification.clock p)).asPolynomial+4)+
      100*((workspace p initial).asPolynomial+1))

theorem routineBudget_le (p initial : PolynomialBound) (n : ℕ) :
    routineBudget M p n (workspace p initial n) ≤ primitiveTime M p initial n := by
  unfold primitiveTime
  apply (PolynomialBound.eval_le_ofPolynomial _ n).trans' ?_
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_C,Polynomial.eval_X,
    Polynomial.eval_ofNat,Polynomial.eval_one,PolynomialBound.asPolynomial_eval]
  unfold routineBudget stepBudget nativeConstant
  rfl

/-- Native primitive-time and store bounds, parameterized by any polynomial
bound on the caller's initial bank. The fixed-width use instantiates `initial`
with the collected block bound. -/
theorem routine_resources (p initial : PolynomialBound) (s : Store M) (bits : BitString) (n : ℕ)
    (coins : s 17 = bits.map (bitSymbol M)) (size : (s 22).length = n)
    (sizes : StoreBound s (initial n)) :
    StoreBound ((routine M p).eval s) (workspace p initial n) ∧
      (routine M p).cost s ≤ primitiveTime M p initial n := by
  have lower := workspace_lower p initial n
  have bigger : initial n ≤ workspace p initial n := by omega
  have bounded := routine_bound M p s bits n (workspace p initial n) coins size (sizes.mono bigger)
    (by omega) (by omega) (by omega) (by omega)
  exact ⟨bounded.1,bounded.2.trans (routineBudget_le M p initial n)⟩

end
end ComplexityOfGenerators.Simulation.StarCertification
