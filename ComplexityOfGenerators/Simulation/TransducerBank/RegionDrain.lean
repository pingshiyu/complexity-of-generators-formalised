import ComplexityOfGenerators.Simulation.TransducerBank.Drain
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.TapeBank

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem drain_inRegion (data : InputData I A) (bits : BitString) (state : Q)
    (table : ∀ input auxiliary index origin cell,
      B.transition state input auxiliary index origin cell = .readRandom state state)
    (fuel : ℕ) (c : BankConfiguration O Q S k) (atState : c.state = state)
    (bound : bits.length ≤ c.randomHead + fuel) (r : ℕ) (bounded : B.Bounded data r c) :
    B.RegionRun data bits r c .exhausted := by
  induction fuel generalizing c with
  | zero =>
      refine ⟨0, c, .refl c bounded, .exhausted c state state ?_ ?_⟩
      · simp [instruction, atState, table]
      · exact List.getElem?_eq_none (by omega)
  | succ fuel ih =>
      cases lookup : bits[c.randomHead]? with
      | none =>
          exact ⟨0, c, .refl c bounded,
            .exhausted c state state (by simp [instruction, atState, table]) lookup⟩
      | some bit =>
          have bounded' : B.Bounded data r (choose c state) :=
            ⟨bounded.input, bounded.auxiliary, bounded.index, bounded.head⟩
          obtain ⟨ticks, finish, path, halt⟩ := ih (choose c state) rfl
            (by change bits.length ≤ c.randomHead + 1 + fuel; omega) bounded'
          refine ⟨ticks + 1, finish, .random c state state bit ticks finish bounded
            (by simp [instruction, atState, table]) lookup ?_, halt⟩
          simpa using path

end ComplexityOfGenerators.Simulation.TransducerBank.TapeBank
