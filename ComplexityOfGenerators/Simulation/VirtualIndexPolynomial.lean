import ComplexityOfGenerators.Simulation.VirtualIndexBootstrap

/-! Polynomial runtime and output preservation for the complete physical-index
adapter used by the collision finder. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

def collisionIndexTimePolynomial (p : PolynomialBound) : Polynomial ℕ :=
  let size : Polynomial ℕ := 4 * (Polynomial.X + 1) + 2
  let time := p.asPolynomial.comp size
  10 * Polynomial.X + 18 + (time + 1) * (2 * time + 2 * size + 8)

def collisionIndexTime (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (collisionIndexTimePolynomial p)

theorem collisionIndexTime_bound (p : PolynomialBound) (n : ℕ) :
    10 * n + 18 + (p (4 * (n + 1) + 2) + 1) *
      (2 * p (4 * (n + 1) + 2) + 2 * (4 * (n + 1) + 2) + 8) ≤ collisionIndexTime p n := by
  simpa [collisionIndexTimePolynomial, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_comp,
    PolynomialBound.asPolynomial_eval, collisionIndexTime] using
    PolynomialBound.eval_le_ofPolynomial (collisionIndexTimePolynomial p) n

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

/-- Every output is preserved on the same finite random tape by the complete
native adapter, including its genuine initialisation from a blank tape. -/
theorem collisionIndexMachine_produces (n : ℕ) (bits : BitString) (word : List O)
    (produces : M.Produces (generatorData (4 * (n + 1) + 2)) bits word) :
    (collisionIndexMachine M).Produces (generatorData n) bits word := by
  obtain ⟨t, execution⟩ := produces
  exact ⟨_, collisionIndexMachine_run M n t bits (.accepted word) execution⟩

/-- A uniform source polynomial gives a uniform target polynomial. All finite
random tapes, including exhausted and overlong tapes, satisfy the time bound. -/
theorem collisionIndexMachine_timeBound (p : PolynomialBound)
    (bound : ∀ n, M.TimeBound (generatorData (4 * (n + 1) + 2)) (p (4 * (n + 1) + 2))) (n : ℕ) :
    (collisionIndexMachine M).TimeBound (generatorData n) (collisionIndexTime p n) := by
  intro bits
  obtain ⟨result, execution⟩ := bound n bits
  have simulated := collisionIndexMachine_run M n (p (4 * (n + 1) + 2)) bits result execution
  have budget := collisionIndexTime_bound p n
  refine ⟨result, ?_⟩
  have padded := (collisionIndexMachine M).run_halted_add (generatorData n) bits _ result simulated
    (collisionIndexTime p n - (10 * n + 18 + (p (4 * (n + 1) + 2) + 1) *
      (2 * p (4 * (n + 1) + 2) + 2 * (4 * (n + 1) + 2) + 8)))
  simpa only [Nat.add_sub_of_le budget] using padded

end

end ComplexityOfGenerators.Simulation
