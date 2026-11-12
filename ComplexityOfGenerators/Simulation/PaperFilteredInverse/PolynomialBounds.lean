import ComplexityOfGenerators.Simulation.PaperFilteredInverse.Bounds

namespace ComplexityOfGenerators.Simulation.PaperFilteredInverse
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α α α) (W : Machine α Unit Unit)

def spacePolynomial (seed time q labelCap : PolynomialBound) : Polynomial ℕ :=
  1+2*Polynomial.X+labelCap.asPolynomial+seed.asPolynomial+
    3*(time.asPolynomial+1)+q.asPolynomial+1

@[simp] theorem spacePolynomial_eval (seed time q labelCap : PolynomialBound) (n : ℕ) :
    (spacePolynomial seed time q labelCap).eval n=
      1+2*n+labelCap n+seed n+3*(time n+1)+q n+1 := by
  simp [spacePolynomial,Polynomial.eval_add,Polynomial.eval_mul]

def costPolynomial (seed time q labelCap : PolynomialBound) : Polynomial ℕ :=
  let cap:=spacePolynomial seed time q labelCap
  29*Polynomial.X+12*seed.asPolynomial+(Command.counterBudget seed).asPolynomial+12+
    (6*Polynomial.X+1+6*labelCap.asPolynomial)+
    Polynomial.C (inverseBodyConstant M W+widthBodyConstant M W+3000)*(cap+1)+
    (Command.counterBudget seed).asPolynomial+(Command.counterBudget time).asPolynomial+
    (Command.counterBudget q).asPolynomial+4*cap+6+seed.asPolynomial

@[simp] theorem costPolynomial_eval (seed time q labelCap : PolynomialBound) (n : ℕ) :
    (costPolynomial M W seed time q labelCap).eval n=
      BoundedSource.prepareBudget seed n+(6*n+1+6*labelCap n)+
      (inverseBodyConstant M W+widthBodyConstant M W+3000)*
        ((spacePolynomial seed time q labelCap).eval n+1)+
      Command.counterBudget seed n+Command.counterBudget time n+Command.counterBudget q n+
      4*(spacePolynomial seed time q labelCap).eval n+6+seed n := by
  simp [costPolynomial,Polynomial.eval_add,Polynomial.eval_mul,BoundedSource.prepareBudget]

theorem controllerBudget_polynomial (seed time q labelCap : PolynomialBound) (n : ℕ)
    (y w : List α) (bits : BitString) (input : y.length≤n) (auxiliary : w.length≤labelCap n) :
    controllerBudget M W seed time q {input:=y,auxiliary:=w,index:=n} bits+seed n≤
      (costPolynomial M W seed time q labelCap).eval n := by
  let cap := (spacePolynomial seed time q labelCap).eval n
  obtain ⟨_,candidate,bodyCost⟩ := body_initial_bound M W seed time q n y w bits cap
    (by dsimp [cap];rw [spacePolynomial_eval];omega)
    (by dsimp [cap];rw [spacePolynomial_eval];omega)
  rw [costPolynomial_eval]
  change BoundedSource.prepareBudget seed n+(6*y.length+1+6*w.length)+
    (body M W seed time q).cost (initialStore M W seed n y w bits)+
    4*(((body M W seed time q).eval (initialStore M W seed n y w bits)) 25).length+6+seed n≤_
  change _≤BoundedSource.prepareBudget seed n+(6*n+1+6*labelCap n)+
    (inverseBodyConstant M W+widthBodyConstant M W+3000)*(cap+1)+
    Command.counterBudget seed n+Command.counterBudget time n+Command.counterBudget q n+4*cap+6+seed n
  omega

def nativeCostPolynomial (seed time q labelCap : PolynomialBound) : Polynomial ℕ :=
  let total := 2*(Polynomial.X+labelCap.asPolynomial)+2+2*costPolynomial M W seed time q labelCap
  1+(total+1)*(2*total+4)

/-- The native clock is uniform in every supplied random tape, including
exhaustion before the prescribed prefix has been collected. -/
theorem native_polynomial_bound (seed time q labelCap : PolynomialBound) :
    ∃ p : PolynomialBound,∀ n (y w : List α) bits,
      y.length≤n→w.length≤labelCap n→
      InputBank.compileBudget (y.length+w.length)
        (controllerBudget M W seed time q {input:=y,auxiliary:=w,index:=n} bits+seed n)≤p n := by
  refine ⟨PolynomialBound.ofPolynomial (nativeCostPolynomial M W seed time q labelCap),?_⟩
  intro n y w bits input auxiliary
  apply le_trans _ (PolynomialBound.eval_le_ofPolynomial _ n)
  have cost := controllerBudget_polynomial M W seed time q labelCap n y w bits input auxiliary
  have arguments : y.length+w.length≤n+labelCap n := Nat.add_le_add input auxiliary
  have total : 2*(y.length+w.length)+2+
      2*(controllerBudget M W seed time q {input:=y,auxiliary:=w,index:=n} bits+seed n)≤
      2*(n+labelCap n)+2+2*(costPolynomial M W seed time q labelCap).eval n := by omega
  simp only [nativeCostPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    PolynomialBound.asPolynomial_eval,Polynomial.eval_ofNat,Polynomial.eval_one,InputBank.compileBudget]
  apply Nat.add_le_add_left
  exact Nat.mul_le_mul (by omega) (by omega)

end
end ComplexityOfGenerators.Simulation.PaperFilteredInverse
