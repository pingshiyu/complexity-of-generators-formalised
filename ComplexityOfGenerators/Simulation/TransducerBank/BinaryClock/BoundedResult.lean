import ComplexityOfGenerators.Simulation.TransducerBank.ExecutionUniqueness

/-! A finite-step specification used to prove the concrete binary-clock
controller. The host recursion is not an instruction of that controller. -/
namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
variable {I A O Q S : Type} {k : ℕ}

def boundedResult (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString) :
    ℕ → BankConfiguration O Q S k → Outcome O
  | 0,_ => .rejected
  | fuel+1,c => match source.instruction data c with
    | .accept => .accepted c.output
    | .reject => .rejected
    | .readRandom no yes => match choices[c.randomHead]? with
      | none => .exhausted
      | some bit => boundedResult source data choices fuel (TapeBank.choose c (if bit then yes else no))
    | .step next write work input auxiliary index emit =>
      boundedResult source data choices fuel (source.advance data c next write work input auxiliary index emit)

theorem boundedResult_accepts (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString)
    (fuel : ℕ) (c : BankConfiguration O Q S k) (word : List O)
    (accepted : boundedResult source data choices fuel c=.accepted word) :
    ∃ ticks, ticks<fuel ∧ source.Executes data choices c ticks (.accepted word) := by
  induction fuel generalizing c with
  | zero => simp [boundedResult] at accepted
  | succ fuel ih =>
    cases table : source.instruction data c with
    | accept =>
      have equal : c.output=word := by simpa [boundedResult,table] using accepted
      exact ⟨0,by omega,by simpa [equal] using TapeBank.Executes.accept c table⟩
    | reject => simp [boundedResult,table] at accepted
    | readRandom no yes =>
      cases lookup : choices[c.randomHead]? with
      | none => simp [boundedResult,table,lookup] at accepted
      | some bit =>
        obtain ⟨ticks,small,run⟩ := ih (TapeBank.choose c (if bit then yes else no))
          (by simpa [boundedResult,table,lookup] using accepted)
        exact ⟨ticks+1,by omega,.random c no yes bit ticks _ table lookup run⟩
    | step next write work input auxiliary index emit =>
      obtain ⟨ticks,small,run⟩ := ih (source.advance data c next write work input auxiliary index emit)
        (by simpa [boundedResult,table] using accepted)
      exact ⟨ticks+1,by omega,.step c next write work input auxiliary index emit ticks _ table run⟩

theorem boundedResult_of_executes (source : TapeBank I A O Q S k)
    {data : InputData I A} {choices : BitString} {c : BankConfiguration O Q S k} {ticks : ℕ} {result : Outcome O}
    (run : source.Executes data choices c ticks result) (fuel : ℕ) (enough : ticks<fuel) :
    boundedResult source data choices fuel c=result := by
  induction run generalizing fuel with
  | accept c table => cases fuel <;> simp_all [boundedResult]
  | reject c table => cases fuel <;> simp_all [boundedResult]
  | exhausted c no yes table absent => cases fuel <;> simp_all [boundedResult]
  | random c no yes bit ticks result table lookup rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simpa [boundedResult,table,lookup] using ih fuel (by omega)
  | step c next write work input auxiliary index emit ticks result table rest ih =>
    cases fuel with
    | zero => omega
    | succ fuel => simpa [boundedResult,table] using ih fuel (by omega)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
