import ComplexityOfGenerators.Simulation.PolynomialClockCorrectness

/-!
# Bounded accepting computations imply NP membership

This is a proved native-machine clocking criterion, not a change to the
definition of NP. The source may run forever on unsuccessful branches; its
compiled machine halts within a uniform polynomial on every finite choice tape.
-/

namespace ComplexityOfGenerators

theorem PolynomialBound.monotone (p : PolynomialBound) : Monotone p := by
  intro n m bound
  exact Nat.mul_le_mul_left p.coefficient (pow_le_pow_left' (by omega) p.degree)

/-- A sound native recognizer with polynomially short accepting witnesses can
be turned into a native nondeterministic polynomial-time decider. -/
theorem np_of_bounded_acceptance {α : Type} [Fintype α] (L : Language α)
    (M : Machine α Bool Unit) (p : PolynomialBound)
    (sound : ∀ w bits, M.Accepts (decisionData w) bits → w ∈ L)
    (complete : ∀ w ∈ L, ∃ bits out, M.run (decisionData w) bits (p w.length) = .halted (.accepted out)) :
    L ∈ NP α := by
  refine ⟨Simulation.polynomialClockMachine M p, Simulation.polynomialClockTime p,
    Simulation.polynomialClockMachine_timeBound M p, fun w => ?_⟩
  constructor
  · rintro ⟨bits, out, accepted⟩
    have source := (Simulation.polynomialClockMachine_produces_iff M p w bits out).mp accepted
    exact sound w bits ⟨out, _, source⟩
  · intro member
    obtain ⟨bits, out, accepted⟩ := complete w member
    have bound := p.monotone (Nat.le_succ w.length)
    have padded := M.run_halted_add (decisionData w) bits (p w.length) (.accepted out) accepted
      (p (w.length + 1) - p w.length)
    refine ⟨bits, out, (Simulation.polynomialClockMachine_produces_iff M p w bits out).mpr ?_⟩
    simpa only [Nat.add_sub_of_le bound] using padded

end ComplexityOfGenerators
