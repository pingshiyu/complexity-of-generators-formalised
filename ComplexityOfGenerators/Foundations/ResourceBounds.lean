import ComplexityOfGenerators.ComplexityClasses
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Polynomial resource calculations

The paper repeatedly uses closure of polynomial bounds under addition,
multiplication and composition. These are concrete upper-bound constructions.
`asPolynomial` connects the local cofinal bound format to Mathlib's polynomials,
the same representation used by Complexitylib's verifier and space algorithms.
-/

namespace ComplexityOfGenerators.PolynomialBound

noncomputable def asPolynomial (p : PolynomialBound) : Polynomial ℕ :=
  Polynomial.C p.coefficient * (Polynomial.X + 1) ^ p.degree

@[simp] theorem asPolynomial_eval (p : PolynomialBound) (n : ℕ) :
    p.asPolynomial.eval n = p n := by
  simp [asPolynomial, PolynomialBound.eval]

theorem positive (p : PolynomialBound) (n : ℕ) : 0 < p n := by
  exact Nat.mul_pos p.coefficient_pos (pow_pos (by omega) _)

/-- Every Mathlib natural-coefficient polynomial admits a bound in the local
format, including at size zero. The added one makes its coefficient positive. -/
noncomputable def ofPolynomial (r : Polynomial ℕ) : PolynomialBound where
  coefficient := r.eval 1 + 1
  degree := r.natDegree
  coefficient_pos := by omega

theorem eval_le_ofPolynomial (r : Polynomial ℕ) (n : ℕ) :
    r.eval n ≤ ofPolynomial r n := by
  have bound : r.eval n ≤ r.eval 1 * (n + 1) ^ r.natDegree := by
    rw [Polynomial.eval_eq_sum_range n, Polynomial.eval_eq_sum_range 1,
      Finset.sum_mul]
    apply Finset.sum_le_sum
    intro i hi
    simp only [one_pow, mul_one]
    apply Nat.mul_le_mul_left
    have degree_bound : i ≤ r.natDegree := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    exact (pow_le_pow_left' (Nat.le_succ n) i).trans
      (pow_le_pow_right' (by omega) degree_bound)
  change r.eval n ≤ (r.eval 1 + 1) * (n + 1) ^ r.natDegree
  exact bound.trans (Nat.mul_le_mul_right _ (Nat.le_succ (r.eval 1)))

def add (p q : PolynomialBound) : PolynomialBound where
  coefficient := p.coefficient + q.coefficient
  degree := p.degree + q.degree
  coefficient_pos := Nat.add_pos_left p.coefficient_pos _

def mul (p q : PolynomialBound) : PolynomialBound where
  coefficient := p.coefficient * q.coefficient
  degree := p.degree + q.degree
  coefficient_pos := Nat.mul_pos p.coefficient_pos q.coefficient_pos

def comp (p q : PolynomialBound) : PolynomialBound where
  coefficient := p.coefficient * (q.coefficient + 1) ^ p.degree
  degree := q.degree * p.degree
  coefficient_pos := Nat.mul_pos p.coefficient_pos (pow_pos (by omega) _)

theorem add_le (p q : PolynomialBound) (n : ℕ) : p n + q n ≤ p.add q n := by
  have base : 1 ≤ n + 1 := by omega
  have hp := pow_le_pow_right' base (Nat.le_add_right p.degree q.degree)
  have hq := pow_le_pow_right' base (Nat.le_add_left q.degree p.degree)
  calc
    p n + q n ≤ p.coefficient * (n + 1) ^ (p.degree + q.degree) +
        q.coefficient * (n + 1) ^ (p.degree + q.degree) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ hp) (Nat.mul_le_mul_left _ hq)
    _ = p.add q n := by simp [add, PolynomialBound.eval, Nat.add_mul]

@[simp] theorem mul_eval (p q : PolynomialBound) (n : ℕ) : p.mul q n = p n * q n := by
  simp [mul, PolynomialBound.eval, pow_add]
  ring

theorem comp_le (p q : PolynomialBound) (n : ℕ) : p (q n) ≤ p.comp q n := by
  have one : 1 ≤ (n + 1) ^ q.degree := one_le_pow₀ (by omega)
  have argument : q n + 1 ≤ (q.coefficient + 1) * (n + 1) ^ q.degree := by
    change q.coefficient * (n + 1) ^ q.degree + 1 ≤ _
    nlinarith
  calc
    p (q n) ≤ p.coefficient * ((q.coefficient + 1) * (n + 1) ^ q.degree) ^ p.degree :=
      Nat.mul_le_mul_left _ (pow_le_pow_left' argument _)
    _ = p.comp q n := by
      simp [comp, PolynomialBound.eval, mul_pow, ← pow_mul, Nat.mul_assoc]

end ComplexityOfGenerators.PolynomialBound
