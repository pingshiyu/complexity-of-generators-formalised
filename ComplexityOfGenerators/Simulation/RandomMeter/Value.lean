import ComplexityOfGenerators.Foundations.StepTranscripts
import ComplexityOfGenerators.Proofs.PaperCertificateBounds

/-! A finite transcript consumes one bit per source instruction: random reads
use that bit, and ordinary instructions ignore it. This is the semantic value
implemented by the native random-meter compiler. -/
namespace ComplexityOfGenerators.Simulation.RandomMeter
variable {I A O : Type} (M : Machine I A O)

def value (data : InputData I A) (c : Configuration M) : BitString → Outcome O
  | [] => match M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
      | .accept => .accepted c.output
      | .reject => .rejected
      | _ => .exhausted
  | bit::tail => match M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
      | .accept => .accepted c.output
      | .reject => .rejected
      | .readRandom no yes => value data {c with state:=if bit then yes else no,randomHead:=0} tail
      | .step next write work input auxiliary index emit =>
          value data (M.stepConfiguration data c next write work input auxiliary index emit) tail

theorem value_accepting (data : InputData I A) (c : Configuration M) (bits : BitString)
    (word : Word O) (accepted : value M data c bits=.accepted word) :
    M.AcceptingTranscript data c bits word := by
  induction bits generalizing c with
  | nil =>
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
      | accept =>
          have same : c.output=word := by simpa [value,action] using accepted
          subst word
          exact .accept c [] action
      | reject => simp [value,action] at accepted
      | readRandom no yes => simp [value,action] at accepted
      | step next write work input auxiliary index emit => simp [value,action] at accepted
  | cons bit tail ih =>
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
      | accept =>
          have same : c.output=word := by simpa [value,action] using accepted
          subst word
          exact .accept c (bit::tail) action
      | reject => simp [value,action] at accepted
      | readRandom no yes =>
          exact .random c bit tail word no yes action (ih _ (by simpa [value,action] using accepted))
      | step next write work input auxiliary index emit =>
          exact .step c bit tail word next write work input auxiliary index emit action
            (ih _ (by simpa [value,action] using accepted))

theorem value_of_accepting {data : InputData I A} {c : Configuration M} {bits : BitString}
    {word : Word O} (trace : M.AcceptingTranscript data c bits word) :
    value M data c bits=.accepted word := by
  induction trace with
  | accept c suffix action => cases suffix <;> simp [value,action]
  | step c bit tail out next write work input auxiliary index emit action rest ih =>
      simpa [value,action] using ih
  | random c bit tail out no yes action rest ih => simpa [value,action] using ih

/-- One source random read can be pulled out of a run. The remainder starts
with a fresh random cursor, on the remaining random tape. -/
theorem choice_runFrom (data : InputData I A) (c : Configuration M) (head : c.randomHead=0)
    (no yes : Fin M.states) (action : M.transition c.state data.input[c.inputHead]?
      data.auxiliary[c.auxiliaryHead]? (if c.indexHead<data.index then some () else none)
      (c.work c.workHead)=.readRandom no yes) (bit : Bool) (bits : BitString) (ticks : ℕ) :
    M.runFrom data (bit::bits) c (ticks+1)=
      M.shiftRandomResult [bit] (M.runFrom data bits {c with state:=if bit then yes else no,randomHead:=0} ticks) := by
  let next : Configuration M := {c with state:=if bit then yes else no,randomHead:=0}
  have live : M.observe data (bit::bits) c=.running c := by simp [Machine.observe,action,head]
  have step : M.next data (bit::bits) c=.running (M.shiftRandomConfiguration [bit] next) := by
    simp [Machine.next,action,head,next,Machine.shiftRandomConfiguration]
  rw [M.runFrom_shift data (bit::bits) c _ live step ticks]
  simpa using M.runFrom_shift_random data [bit] bits next ticks

/-- If all actual source tapes halt by a deadline and never reject, then every
transcript longer than that deadline reaches acceptance. This derives the
full-trial property rather than assuming it as a generator requirement. -/
theorem value_accepts_of_total (data : InputData I A) (ticks : ℕ) (c : Configuration M)
    (head : c.randomHead=0)
    (total : ∀ bits : BitString,∃ result,M.runFrom data bits c ticks=.halted result)
    (noReject : ∀ bits : BitString,∀ t,M.runFrom data bits c t≠.halted .rejected)
    (bits : BitString) (long : ticks<bits.length) :
    ∃ word,value M data c bits=.accepted word := by
  induction ticks generalizing c bits with
  | zero =>
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
      | accept => exact ⟨c.output,by cases bits <;> simp [value,action]⟩
      | reject => exact False.elim (noReject [] 0 (by simp [Machine.runFrom,Machine.observe,action]))
      | readRandom no yes =>
          obtain ⟨result,halted⟩ := total [false]
          simp [Machine.runFrom,Machine.observe,action,head] at halted
      | step next write work input auxiliary index emit =>
          obtain ⟨result,halted⟩ := total []
          simp [Machine.runFrom,Machine.observe,action] at halted
  | succ ticks ih =>
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
      | accept => exact ⟨c.output,by cases bits <;> simp [value,action]⟩
      | reject => exact False.elim (noReject [] 0 (by simp [Machine.runFrom,Machine.observe,action]))
      | step next write work input auxiliary index emit =>
          cases bits with
          | nil => simp at long
          | cons bit tail =>
              let finish := M.stepConfiguration data c next write work input auxiliary index emit
              have live (seed : BitString) : M.observe data seed c=.running c :=
                M.observe_step data seed c _ _ _ _ _ _ _ action
              have step (seed : BitString) : M.next data seed c=.running finish :=
                M.next_step data seed c _ _ _ _ _ _ _ action
              have total' : ∀ seed : BitString,∃ result,M.runFrom data seed finish ticks=.halted result := by
                intro seed
                obtain ⟨result,run⟩ := total seed
                exact ⟨result,by simpa only [M.runFrom_shift data seed c finish (live seed) (step seed) ticks] using run⟩
              have noReject' : ∀ seed : BitString,∀ t,M.runFrom data seed finish t≠.halted .rejected := by
                intro seed t rejected
                apply noReject seed (t+1)
                rw [M.runFrom_shift data seed c finish (live seed) (step seed) t,rejected]
              obtain ⟨word,accepted⟩ := ih finish (by simp [finish,Machine.stepConfiguration,head]) total' noReject'
                tail (by simp only [List.length_cons] at long;omega)
              exact ⟨word,by simpa only [value,action] using accepted⟩
      | readRandom no yes =>
          cases bits with
          | nil => simp at long
          | cons bit tail =>
              let finish : Configuration M := {c with state:=if bit then yes else no,randomHead:=0}
              have total' : ∀ seed : BitString,∃ result,M.runFrom data seed finish ticks=.halted result := by
                intro seed
                obtain ⟨result,run⟩ := total (bit::seed)
                rw [choice_runFrom M data c head no yes action bit seed ticks] at run
                cases execution : M.runFrom data seed finish ticks with
                | running d => simp only [finish,execution,Machine.shiftRandomResult] at run;cases run
                | halted result => exact ⟨result,rfl⟩
              have noReject' : ∀ seed : BitString,∀ t,M.runFrom data seed finish t≠.halted .rejected := by
                intro seed t rejected
                apply noReject (bit::seed) (t+1)
                rw [choice_runFrom M data c head no yes action bit seed t]
                change M.shiftRandomResult [bit] (M.runFrom data seed finish t)=_
                rw [rejected]
                rfl
              obtain ⟨word,accepted⟩ := ih finish rfl total' noReject' tail
                (by simp only [List.length_cons] at long;omega)
              exact ⟨word,by simpa only [value,action] using accepted⟩

end ComplexityOfGenerators.Simulation.RandomMeter
