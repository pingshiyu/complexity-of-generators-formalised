import ComplexityOfGenerators.Simulation.TransducerBank.Embedding
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q Q' S : Type} {k : ℕ}
  (B : TapeBank I A O Q S k) (C : TapeBank I A O Q' S k) (f : Q → Q')

theorem RegionSteps.mapState (selected : ∀ q, C.select (f q) = B.select q)
    (steps : ∀ q i a x origin cell next write work input auxiliary index emit,
      B.transition q i a x origin cell = .step next write work input auxiliary index emit →
      C.transition (f q) i a x origin cell = .step (f next) write work input auxiliary index emit)
    (random : ∀ q i a x origin cell no yes,
      B.transition q i a x origin cell = .readRandom no yes →
      C.transition (f q) i a x origin cell = .readRandom (f no) (f yes))
    {data : InputData I A} {bits : BitString} {c d : BankConfiguration O Q S k} {r t : ℕ}
    (path : B.RegionSteps data bits r c t d) :
    C.RegionSteps data bits r (c.mapState f) t (d.mapState f) := by
  induction path with
  | refl c bound => exact .refl _ ⟨bound.input, bound.auxiliary, bound.index, bound.head⟩
  | random c no yes bit t d bound table lookup rest ih =>
      have target : C.instruction data (c.mapState f) = .readRandom (f no) (f yes) := by
        simp only [instruction, BankConfiguration.mapState, selected] at table ⊢
        exact random _ _ _ _ _ _ _ _ table
      have bounded : C.Bounded data r (c.mapState f) := ⟨bound.input, bound.auxiliary, bound.index, bound.head⟩
      apply RegionSteps.random (c.mapState f) (f no) (f yes) bit t (d.mapState f) bounded target lookup
      simpa only [choose, BankConfiguration.mapState, apply_ite f] using ih
  | step c next write work input auxiliary index emit t d bound table rest ih =>
      have target : C.instruction data (c.mapState f) = .step (f next) write work input auxiliary index emit := by
        simp only [instruction, BankConfiguration.mapState, selected] at table ⊢
        exact steps _ _ _ _ _ _ _ _ _ _ _ _ _ table
      have bounded : C.Bounded data r (c.mapState f) := ⟨bound.input, bound.auxiliary, bound.index, bound.head⟩
      apply RegionSteps.step (c.mapState f) (f next) write work input auxiliary index emit t (d.mapState f) bounded target
      rw [advance_mapState B C f selected]
      exact ih

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
