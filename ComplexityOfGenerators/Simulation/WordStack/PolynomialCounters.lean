import ComplexityOfGenerators.Simulation.WordStack.Unary

/-! Uniform polynomial counters. Coefficients and exponents occur in the finite
program; the input-dependent value is computed by unary stack operations. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Command

variable {S O : Type} {k : ℕ}

def loadSize (base : Fin k) (unit : S) : Command S O k :=
  (loadIndex base unit).seq (push base unit)

theorem loadSize_runs (base : Fin k) (unit : S) (n : ℕ) (bits : BitString)
    (m : Memory S O k) (origin : m.indexHead = 0) (empty : m.store base = []) :
    (loadSize base unit).Runs n bits m (3 * n + 2)
      (.done {m.set base (List.replicate (n + 1) unit) with indexHead := n}) := by
  have first := loadIndex_runs base unit n bits m (by omega)
  have last := push_runs base unit (n := n) bits (loadedIndex base unit n m) (by simp [loadedIndex])
  have final : (loadedIndex base unit n m).set base (unit :: (loadedIndex base unit n m).store base) =
      {m.set base (List.replicate (n + 1) unit) with indexHead := n} := by
    apply Configuration.ext <;> simp [loadedIndex, Memory.set, origin, empty, List.replicate_succ]
  rw [final] at last
  have run := Runs.seq _ _ _ _ _ _ _ first last
  convert run using 1
  · rfl
  · simp [origin]

def polynomialCounter (p : PolynomialBound) (value base temp scratch : Fin k) (unit : S) : Command S O k :=
  (clear value).seq ((prepend value (List.replicate p.coefficient unit)).seq
    (power value base temp scratch p.degree))

def counterTicks (p : PolynomialBound) (n old : ℕ) : ℕ :=
  3 * old + 2 * p.coefficient + powerTime p.coefficient (n + 1) p.degree + 2

theorem polynomialCounter_runs (p : PolynomialBound) (value base temp scratch : Fin k)
    (vb : value ≠ base) (vt : value ≠ temp) (vs : value ≠ scratch)
    (bt : base ≠ temp) (bs : base ≠ scratch) (ts : temp ≠ scratch)
    (unit : S) (n : ℕ) {index : ℕ} (bits : BitString) (m : Memory S O k) (bounded : m.indexHead ≤ index)
    (base_eq : m.store base = List.replicate (n + 1) unit)
    (temp_eq : m.store temp = []) (scratch_eq : m.store scratch = []) :
    (polynomialCounter p value base temp scratch unit).Runs index bits m (counterTicks p n (m.store value).length)
      (.done (m.set value (List.replicate (p n) unit))) := by
  have clearStep := clear_runs value bits m bounded
  have initial := prepend_runs value (List.replicate p.coefficient unit) bits (m.set value []) bounded
  simp only [Memory.set_here, Memory.set_twice, List.append_nil, List.length_replicate] at initial
  have powerStep := power_runs value base temp scratch vb vt vs bt bs ts unit p.coefficient (n + 1) p.degree
    bits (m.set value (List.replicate p.coefficient unit)) bounded (by simp)
    (by simp [vb.symm, base_eq]) (by simp [vt.symm, temp_eq]) (by simp [vs.symm, scratch_eq])
  simp only [Memory.set_twice] at powerStep
  have body := Runs.seq _ _ _ _ _ _ _ initial powerStep
  have run := Runs.seq _ _ _ _ _ _ _ clearStep body
  convert run using 1
  · rfl
  · simp only [counterTicks]; omega
  · rfl

noncomputable def counterBudget (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (Polynomial.C (2 * p.coefficient) +
    Polynomial.C p.degree * (p.asPolynomial * (20 * (Polynomial.X + 1) + 5) + 2) + 2)

theorem counterTicks_bound (p : PolynomialBound) (n old : ℕ) :
    counterTicks p n old ≤ 3 * old + counterBudget p n := by
  have power := powerTime_bound p.coefficient (n + 1) p.degree (by omega)
  have polynomial := PolynomialBound.eval_le_ofPolynomial
    (Polynomial.C (2 * p.coefficient) +
      Polynomial.C p.degree * (p.asPolynomial * (20 * (Polynomial.X + 1) + 5) + 2) + 2) n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_ofNat,
    Polynomial.eval_X, Polynomial.eval_one, PolynomialBound.asPolynomial_eval] at polynomial
  change _ ≤ counterBudget p n at polynomial
  simp only [counterTicks]
  change powerTime p.coefficient (n + 1) p.degree ≤ p.degree * (p n * (20 * (n + 1) + 5) + 2) at power
  omega

end ComplexityOfGenerators.Simulation.WordStack.Command
