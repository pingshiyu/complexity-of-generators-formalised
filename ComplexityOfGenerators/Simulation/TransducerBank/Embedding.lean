import ComplexityOfGenerators.Simulation.TransducerBank.Execution

/-! Embedding a bank program in larger finite control. Nonterminal paths are
preserved even when the larger program replaces halting with a continuation. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank

variable {I A O Q Q' S : Type} {k : ℕ}

def BankConfiguration.mapState (f : Q → Q') (c : BankConfiguration O Q S k) : BankConfiguration O Q' S k :=
  ⟨f c.state, c.inputHead, c.auxiliaryHead, c.indexHead, c.randomHead, c.output, c.head, c.tape⟩

namespace TapeBank

variable (B : TapeBank I A O Q S k) (C : TapeBank I A O Q' S k) (f : Q → Q')

theorem advance_mapState (selected : ∀ q, C.select (f q) = B.select q)
    (data : InputData I A) (c : BankConfiguration O Q S k)
    (next write work input auxiliary index emit) :
    C.advance data (c.mapState f) (f next) write work input auxiliary index emit =
      (B.advance data c next write work input auxiliary index emit).mapState f := by
  simp [advance, BankConfiguration.mapState, selected]

/-- Only ordinary and successful random transitions need to agree. -/
theorem Steps.mapState (selected : ∀ q, C.select (f q) = B.select q)
    (steps : ∀ q i a x origin cell next write work input auxiliary index emit,
      B.transition q i a x origin cell = .step next write work input auxiliary index emit →
      C.transition (f q) i a x origin cell = .step (f next) write work input auxiliary index emit)
    (random : ∀ q i a x origin cell no yes,
      B.transition q i a x origin cell = .readRandom no yes →
      C.transition (f q) i a x origin cell = .readRandom (f no) (f yes))
    {data : InputData I A} {bits : BitString} {c d : BankConfiguration O Q S k} {t : ℕ}
    (path : B.Steps data bits c t d) : C.Steps data bits (c.mapState f) t (d.mapState f) := by
  induction path with
  | refl c => exact .refl _
  | random c no yes bit t d table lookup rest ih =>
      have target : C.instruction data (c.mapState f) = .readRandom (f no) (f yes) := by
        simp only [instruction, BankConfiguration.mapState, selected] at table ⊢
        exact random _ _ _ _ _ _ _ _ table
      apply Steps.random _ _ _ bit t _ target lookup
      simpa only [choose, BankConfiguration.mapState, apply_ite f] using ih
  | step c next write work input auxiliary index emit t d table rest ih =>
      have target : C.instruction data (c.mapState f) = .step (f next) write work input auxiliary index emit := by
        simp only [instruction, BankConfiguration.mapState, selected] at table ⊢
        exact steps _ _ _ _ _ _ _ _ _ _ _ _ _ table
      apply Steps.step _ _ _ _ _ _ _ _ t _ target
      rw [advance_mapState B C f selected]
      exact ih

/-- An exhausted execution consists of a finite nonterminal path followed by
an attempted read at the end of the random tape. -/
theorem Executes.exhausted_path {data : InputData I A} {bits : BitString}
    {c : BankConfiguration O Q S k} {t : ℕ} {result : Outcome O}
    (execution : B.Executes data bits c t result) (exhausted : result = .exhausted) :
    ∃ d no yes, B.Steps data bits c t d ∧ B.instruction data d = .readRandom no yes ∧ bits[d.randomHead]? = none := by
  induction execution with
  | accept => cases exhausted
  | reject => cases exhausted
  | exhausted c no yes table absent => exact ⟨c, no, yes, .refl _, table, absent⟩
  | random c no yes bit t result table lookup rest ih =>
      obtain ⟨d, no', yes', path, final, absent⟩ := ih exhausted
      exact ⟨d, no', yes', .random _ no yes bit _ _ table lookup path, final, absent⟩
  | step c next write work input auxiliary index emit t result table rest ih =>
      obtain ⟨d, no, yes, path, final, absent⟩ := ih exhausted
      exact ⟨d, no, yes, .step _ next write work input auxiliary index emit _ _ table path, final, absent⟩

end TapeBank
end ComplexityOfGenerators.Simulation.TransducerBank
