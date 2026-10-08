import ComplexityOfGenerators.Foundations.RandomTapeShift
import ComplexityOfGenerators.Foundations.ExecutionBounds

/-!
# Finite accepting transcripts of a native machine

One transcript bit is associated with every nonterminal step. On an ordinary
step its value is ignored; on a random read it selects the branch. Halting does
not need a transcript bit. The relation is operational: each constructor uses
one instruction of the original finite transition table.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

inductive AcceptingTranscript (data : InputData I A) : Configuration M → BitString → List O → Prop
  | accept (c : Configuration M) (suffix : BitString)
      (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some true else none) (c.work c.workHead) = .accept) :
      AcceptingTranscript data c suffix c.output
  | step (c : Configuration M) (bit : Bool) (tail : BitString) (out : List O)
      (state : Fin M.states) (write : Option (Fin M.symbols))
      (work input auxiliary index : Move) (emit : Option O)
      (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
        .step state write work input auxiliary index emit)
      (rest : AcceptingTranscript data
        (M.stepConfiguration data c state write work input auxiliary index emit) tail out) :
      AcceptingTranscript data c (bit :: tail) out
  | random (c : Configuration M) (bit : Bool) (tail : BitString) (out : List O)
      (no yes : Fin M.states)
      (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some true else none) (c.work c.workHead) = .readRandom no yes)
      (rest : AcceptingTranscript data {c with state := if bit then yes else no, randomHead := 0} tail out) :
      AcceptingTranscript data c (bit :: tail) out

/-- Every accepting transcript is realised by a genuine finite random tape.
Only bits at random-read instructions enter that tape. -/
theorem AcceptingTranscript.realize {data : InputData I A} {c : Configuration M}
    {transcript : BitString} {out : List O} (trace : M.AcceptingTranscript data c transcript out)
    (head : c.randomHead = 0) :
    ∃ bits t, t ≤ transcript.length ∧ M.runFrom data bits c t = .halted (.accepted out) := by
  induction trace with
  | accept c suffix action =>
      exact ⟨[], 0, Nat.zero_le _, by simp [runFrom, observe, action]⟩
  | step c bit tail out state write work input auxiliary index emit action rest ih =>
      obtain ⟨bits, t, length, accepted⟩ := ih head
      have live := M.observe_step data bits c state write work input auxiliary index emit action
      have next := M.next_step data bits c state write work input auxiliary index emit action
      exact ⟨bits, t + 1, by simp only [List.length_cons]; omega,
        (M.runFrom_shift data bits c _ live next t).trans accepted⟩
  | random c bit tail out no yes action rest ih =>
      obtain ⟨bits, t, length, accepted⟩ := ih rfl
      let d : Configuration M := {c with state := if bit then yes else no, randomHead := 0}
      have live : M.observe data (bit :: bits) c = .running c := by
        simp [observe, action, head]
      have next : M.next data (bit :: bits) c = .running (M.shiftRandomConfiguration [bit] d) := by
        simp [Machine.next, action, head, d, shiftRandomConfiguration]
      have shifted := M.runFrom_shift_random data [bit] bits d t
      rw [accepted] at shifted
      refine ⟨bit :: bits, t + 1, by simp only [List.length_cons]; omega, ?_⟩
      rw [M.runFrom_shift data (bit :: bits) c _ live next t]
      exact shifted

/-- No new recognition semantics is assumed: a transcript starting on the
blank native configuration implies ordinary native acceptance. -/
theorem AcceptingTranscript.produces {data : InputData I A} {transcript : BitString} {out : List O}
    (trace : M.AcceptingTranscript data M.initialConfiguration transcript out) :
    ∃ bits, M.Produces data bits out := by
  obtain ⟨bits, t, _, accepted⟩ := trace.realize M rfl
  exact ⟨bits, t, by simpa only [runFrom_initial] using accepted⟩

def resetRandom (c : Configuration M) : Configuration M := {c with randomHead := 0}

private theorem transcript_of_accepting_observation (data : InputData I A) (bits : BitString)
    (c : Configuration M) (out : List O) (accepted : M.observe data bits c = .halted (.accepted out)) :
    M.AcceptingTranscript data (M.resetRandom c) [] out := by
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | accept =>
      have equal : c.output = out := by simpa [observe, action] using accepted
      rw [← equal]
      exact .accept _ [] action
  | reject => simp [observe, action] at accepted
  | step state write work input auxiliary index emit => simp [observe, action] at accepted
  | readRandom no yes =>
      simp only [observe, action] at accepted
      split_ifs at accepted
      cases accepted

/-- Conversely, every accepting native run supplies a transcript with at most
one bit per elapsed primitive transition. The random cursor is bookkeeping,
so the transcript relation normalises it to zero. -/
theorem acceptingTranscript_of_runFrom (data : InputData I A) (bits : BitString)
    (c : Configuration M) (t : ℕ) (out : List O)
    (accepted : M.runFrom data bits c t = .halted (.accepted out)) :
    ∃ transcript, transcript.length ≤ t ∧ M.AcceptingTranscript data (M.resetRandom c) transcript out := by
  induction t generalizing c with
  | zero => exact ⟨[], le_rfl, transcript_of_accepting_observation M data bits c out accepted⟩
  | succ t ih =>
      cases observation : M.observe data bits c with
      | halted result =>
          have atClock := M.runFrom_halted data bits c result observation (t + 1)
          rw [accepted] at atClock
          cases atClock
          exact ⟨[], Nat.zero_le _, transcript_of_accepting_observation M data bits c out observation⟩
      | running d =>
          have same := M.observe_running_eq data bits c d observation
          subst d
          obtain ⟨d, step⟩ := M.next_running_of_observe_running data bits c observation
          rw [M.runFrom_shift data bits c d observation step t] at accepted
          obtain ⟨trace, length, continuation⟩ := ih d accepted
          cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
              (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
          | accept => simp [observe, action] at observation
          | reject => simp [observe, action] at observation
          | step state write work input auxiliary index emit =>
              rw [M.next_step data bits c state write work input auxiliary index emit action] at step
              cases step
              refine ⟨false :: trace, by simp only [List.length_cons]; omega, ?_⟩
              apply AcceptingTranscript.step (M.resetRandom c) false trace out state write work input auxiliary index emit action
              simpa only [resetRandom, stepConfiguration] using continuation
          | readRandom no yes =>
              cases lookup : bits[c.randomHead]? with
              | none => simp [next, action, lookup] at step
              | some bit =>
                  simp only [next, action, lookup, RunState.running.injEq] at step
                  subst d
                  refine ⟨bit :: trace, by simp only [List.length_cons]; omega, ?_⟩
                  exact .random _ bit trace out no yes action continuation

theorem produces_iff_acceptingTranscript (data : InputData I A) (out : List O) :
    (∃ bits, M.Produces data bits out) ↔
      ∃ transcript, M.AcceptingTranscript data M.initialConfiguration transcript out := by
  constructor
  · rintro ⟨bits, t, accepted⟩
    obtain ⟨trace, _, transcript⟩ := M.acceptingTranscript_of_runFrom data bits M.initialConfiguration t out
      (by simpa only [runFrom_initial] using accepted)
    exact ⟨trace, transcript⟩
  · rintro ⟨trace, accepted⟩
    exact accepted.produces M

end ComplexityOfGenerators.Machine
