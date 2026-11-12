import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

/-! A fixed finite product of tracks is one finite work alphabet. Selecting
one track changes no other track and adds no work-head or space overhead. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.Tracks

set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k tracks : ℕ}

def instruction (track : Fin tracks) (cell : Fin tracks→S) :
    BankInstruction Q S O → BankInstruction Q (Fin tracks→S) O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom no yes
  | .step next write work input auxiliary index emit =>
      .step next (Function.update cell track write) work input auxiliary index emit

def bank (source : TapeBank I A O Q S k) (track : Fin tracks) : TapeBank I A O Q (Fin tracks→S) k where
  initial := source.initial
  blank := fun _ => source.blank
  select := source.select
  transition := fun state input auxiliary index origin cell =>
    instruction track cell (source.transition state input auxiliary index origin (cell track))

def lift (track : Fin tracks) (other : Fin k→ℤ→Fin tracks→S)
    (configuration : BankConfiguration O Q S k) : BankConfiguration O Q (Fin tracks→S) k :=
  ⟨configuration.state,configuration.inputHead,configuration.auxiliaryHead,configuration.indexHead,
    configuration.randomHead,configuration.output,configuration.head,
    fun tape position => Function.update (other tape position) track (configuration.tape tape position)⟩

theorem instruction_lift (source : TapeBank I A O Q S k) (track : Fin tracks)
    (other : Fin k→ℤ→Fin tracks→S) (data : InputData I A) (configuration : BankConfiguration O Q S k) :
    (bank source track).instruction data (lift track other configuration)=
      instruction track ((lift track other configuration).tape (source.select configuration.state)
        (configuration.head (source.select configuration.state))) (source.instruction data configuration) := by
  simp [TapeBank.instruction,bank,lift]

theorem advance_lift (source : TapeBank I A O Q S k) (track : Fin tracks)
    (other : Fin k→ℤ→Fin tracks→S) (data : InputData I A) (configuration : BankConfiguration O Q S k)
    (next write work input auxiliary index emit) :
    (bank source track).advance data (lift track other configuration) next
        (Function.update ((lift track other configuration).tape (source.select configuration.state)
          (configuration.head (source.select configuration.state))) track write)
        work input auxiliary index emit=
      lift track other (source.advance data configuration next write work input auxiliary index emit) := by
  apply BankConfiguration.ext <;> try rfl
  funext tape position chosen
  by_cases sameTape : tape=source.select configuration.state
  · subst tape
    by_cases samePosition : position=configuration.head (source.select configuration.state)
    · subst position
      simp [TapeBank.advance,lift,bank,Function.update_idem]
    · simp [TapeBank.advance,lift,bank,Function.update_of_ne samePosition]
  · simp [TapeBank.advance,lift,bank,Function.update_of_ne sameTape]

theorem choose_lift (track : Fin tracks) (other : Fin k→ℤ→Fin tracks→S)
    (configuration : BankConfiguration O Q S k) (next : Q) :
    TapeBank.choose (lift track other configuration) next=lift track other (TapeBank.choose configuration next) := rfl

theorem bounded_lift (source : TapeBank I A O Q S k) (track : Fin tracks)
    (other : Fin k→ℤ→Fin tracks→S) (data : InputData I A) (radius : ℕ)
    (configuration : BankConfiguration O Q S k) (bounded : source.Bounded data radius configuration) :
    (bank source track).Bounded data radius (lift track other configuration) :=
  ⟨bounded.input,bounded.auxiliary,bounded.index,bounded.head⟩

theorem steps_lift (source : TapeBank I A O Q S k) (track : Fin tracks)
    (other : Fin k→ℤ→Fin tracks→S) {data : InputData I A} {choices : BitString}
    {start finish : BankConfiguration O Q S k} {time : ℕ} (path : source.Steps data choices start time finish) :
    (bank source track).Steps data choices (lift track other start) time (lift track other finish) := by
  induction path with
  | refl start => exact .refl _
  | random start no yes bit time finish table lookup rest ih =>
      apply TapeBank.Steps.random _ no yes bit time _
      · rw [instruction_lift,table]
        rfl
      · exact lookup
      · rw [choose_lift]
        exact ih
  | step start next write work input auxiliary index emit time finish table rest ih =>
      apply TapeBank.Steps.step _ next _ work input auxiliary index emit time _
      · rw [instruction_lift,table]
        rfl
      · rw [advance_lift]
        exact ih

theorem regionSteps_lift (source : TapeBank I A O Q S k) (track : Fin tracks)
    (other : Fin k→ℤ→Fin tracks→S) {data : InputData I A} {choices : BitString}
    {start finish : BankConfiguration O Q S k} {radius time : ℕ}
    (path : source.RegionSteps data choices radius start time finish) :
    (bank source track).RegionSteps data choices radius (lift track other start) time (lift track other finish) := by
  induction path with
  | refl start bounded => exact .refl _ (bounded_lift source track other data radius start bounded)
  | random start no yes bit time finish bounded table lookup rest ih =>
      apply TapeBank.RegionSteps.random _ no yes bit time _ (bounded_lift source track other data radius start bounded)
      · rw [instruction_lift,table]
        rfl
      · exact lookup
      · rw [choose_lift]
        exact ih
  | step start next write work input auxiliary index emit time finish bounded table rest ih =>
      apply TapeBank.RegionSteps.step _ next _ work input auxiliary index emit time _
        (bounded_lift source track other data radius start bounded)
      · rw [instruction_lift,table]
        rfl
      · rw [advance_lift]
        exact ih

theorem executes_lift (source : TapeBank I A O Q S k) (track : Fin tracks)
    (other : Fin k→ℤ→Fin tracks→S) {data : InputData I A} {choices : BitString}
    {start : BankConfiguration O Q S k} {time : ℕ} {result : Outcome O}
    (run : source.Executes data choices start time result) :
    (bank source track).Executes data choices (lift track other start) time result := by
  induction run with
  | accept start table =>
      apply TapeBank.Executes.accept
      rw [instruction_lift,table]
      rfl
  | reject start table =>
      apply TapeBank.Executes.reject
      rw [instruction_lift,table]
      rfl
  | exhausted start no yes table absent =>
      apply TapeBank.Executes.exhausted _ no yes
      · rw [instruction_lift,table]
        rfl
      · exact absent
  | random start no yes bit time result table lookup rest ih =>
      apply TapeBank.Executes.random _ no yes bit time result
      · rw [instruction_lift,table]
        rfl
      · exact lookup
      · rw [choose_lift]
        exact ih
  | step start next write work input auxiliary index emit time result table rest ih =>
      apply TapeBank.Executes.step _ next _ work input auxiliary index emit time result
      · rw [instruction_lift,table]
        rfl
      · rw [advance_lift]
        exact ih

end ComplexityOfGenerators.Simulation.TransducerBank.Tracks
