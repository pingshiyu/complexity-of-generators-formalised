import ComplexityOfGenerators.Simulation.TransducerBank.Embedding

namespace ComplexityOfGenerators.Simulation.TransducerBank

variable {I A O Q Q' S : Type} {k : ℕ}

def BankInstruction.mapState (f : Q → Q') : BankInstruction Q S O → BankInstruction Q' S O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (f no) (f yes)
  | .step next write work input auxiliary index emit =>
      .step (f next) write work input auxiliary index emit

namespace TapeBank

 theorem Executes.mapState (B : TapeBank I A O Q S k) (C : TapeBank I A O Q' S k)
    (f : Q → Q') (selected : ∀ q,C.select (f q)=B.select q)
    (table : ∀ q i a x origin cell,
      C.transition (f q) i a x origin cell=(B.transition q i a x origin cell).mapState f)
    {data : InputData I A} {bits : BitString} {c : BankConfiguration O Q S k}
    {ticks : ℕ} {result : Outcome O} (run : B.Executes data bits c ticks result) :
    C.Executes data bits (c.mapState f) ticks result := by
  have instruction : ∀ c, C.instruction data (c.mapState f)=(B.instruction data c).mapState f := by
    intro c
    simp only [TapeBank.instruction,BankConfiguration.mapState,selected,table]
    rfl
  induction run with
  | accept c source =>
      apply Executes.accept
      rw [instruction,source]; rfl
  | reject c source =>
      apply Executes.reject
      rw [instruction,source]; rfl
  | exhausted c no yes source absent =>
      apply Executes.exhausted _ (f no) (f yes)
      · rw [instruction,source]; rfl
      · exact absent
  | random c no yes bit ticks result source lookup rest ih =>
      apply Executes.random _ (f no) (f yes) bit ticks result
      · rw [instruction,source]; rfl
      · exact lookup
      · simpa only [choose,BankConfiguration.mapState,apply_ite f] using ih
  | step c next write work input auxiliary index emit ticks result source rest ih =>
      apply Executes.step _ (f next) write work input auxiliary index emit ticks result
      · rw [instruction,source]; rfl
      · rw [advance_mapState B C f selected]
        exact ih

end TapeBank
end ComplexityOfGenerators.Simulation.TransducerBank
