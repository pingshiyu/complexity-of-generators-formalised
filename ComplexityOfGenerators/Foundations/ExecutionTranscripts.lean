import ComplexityOfGenerators.Foundations.StepTranscripts

/-!
# Transcripts of terminating runs on a fixed random tape

Unlike `AcceptingTranscript`, this relation records the actual choices of a
specified tape, ends at the first terminal observation, and includes rejection
and exhaustion. Ordinary steps record `false`; random steps record their bit.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

inductive ExecutionTranscript (data : InputData I A) (bits : BitString) :
    Configuration M → BitString → Outcome O → Prop
  | halt (c : Configuration M) (outcome : Outcome O)
      (terminal : M.observe data bits c = .halted outcome) :
      ExecutionTranscript data bits c [] outcome
  | step (c : Configuration M) (tail : BitString) (outcome : Outcome O)
      (state : Fin M.states) (write : Option (Fin M.symbols))
      (work input auxiliary index : Move) (emit : Option O)
      (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
        .step state write work input auxiliary index emit)
      (rest : ExecutionTranscript data bits
        (M.stepConfiguration data c state write work input auxiliary index emit) tail outcome) :
      ExecutionTranscript data bits c (false :: tail) outcome
  | random (c : Configuration M) (bit : Bool) (tail : BitString) (outcome : Outcome O)
      (no yes : Fin M.states)
      (action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some true else none) (c.work c.workHead) = .readRandom no yes)
      (lookup : bits[c.randomHead]? = some bit)
      (rest : ExecutionTranscript data bits
        {c with state := if bit then yes else no, randomHead := c.randomHead + 1} tail outcome) :
      ExecutionTranscript data bits c (bit :: tail) outcome

/-- Recording never adds bits after the source has halted. -/
theorem executionTranscript_of_runFrom (data : InputData I A) (bits : BitString)
    (c : Configuration M) (t : ℕ) (outcome : Outcome O)
    (halted : M.runFrom data bits c t = .halted outcome) :
    ∃ log, log.length ≤ t ∧ M.ExecutionTranscript data bits c log outcome := by
  induction t generalizing c with
  | zero => exact ⟨[], le_rfl, .halt c outcome halted⟩
  | succ t ih =>
      cases observation : M.observe data bits c with
      | halted result =>
          have same := M.runFrom_halted data bits c result observation (t + 1)
          rw [halted] at same
          cases same
          exact ⟨[], Nat.zero_le _, .halt c outcome observation⟩
      | running d =>
          have same := M.observe_running_eq data bits c d observation
          subst d
          obtain ⟨d, next⟩ := M.next_running_of_observe_running data bits c observation
          rw [M.runFrom_shift data bits c d observation next t] at halted
          obtain ⟨log, length, recorded⟩ := ih d halted
          cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
              (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
          | accept => simp [observe, action] at observation
          | reject => simp [observe, action] at observation
          | step state write work input auxiliary index emit =>
              rw [M.next_step data bits c state write work input auxiliary index emit action] at next
              cases next
              exact ⟨false :: log, by simp only [List.length_cons]; omega,
                .step c log outcome state write work input auxiliary index emit action recorded⟩
          | readRandom no yes =>
              cases lookup : bits[c.randomHead]? with
              | none => simp [Machine.next, action, lookup] at next
              | some bit =>
                  simp only [Machine.next, action, lookup, RunState.running.injEq] at next
                  subst d
                  exact ⟨bit :: log, by simp only [List.length_cons]; omega,
                    .random c bit log outcome no yes action lookup recorded⟩

/-- The recorded execution can be replayed with exactly one step per bit. -/
theorem ExecutionTranscript.run {data : InputData I A} {bits : BitString}
    {c : Configuration M} {log : BitString} {outcome : Outcome O}
    (recorded : M.ExecutionTranscript data bits c log outcome) :
    M.runFrom data bits c log.length = .halted outcome := by
  induction recorded with
  | halt c outcome terminal => exact terminal
  | step c tail outcome state write work input auxiliary index emit action rest ih =>
      rw [List.length_cons, M.runFrom_shift data bits c _
        (M.observe_step data bits c _ _ _ _ _ _ _ action)
        (M.next_step data bits c _ _ _ _ _ _ _ action)]
      exact ih
  | random c bit tail outcome no yes action lookup rest ih =>
      have available : c.randomHead < bits.length := List.getElem?_eq_some_iff.mp lookup |>.1
      have live : M.observe data bits c = .running c := by simp [observe, action, available]
      have next : M.next data bits c = .running
          {c with state := if bit then yes else no, randomHead := c.randomHead + 1} := by
        simp [Machine.next, action, lookup]
      rw [List.length_cons, M.runFrom_shift data bits c _ live next]
      exact ih

/-- Accepted recordings are certificates in the operational replay relation. -/
theorem ExecutionTranscript.accepting {data : InputData I A} {bits : BitString}
    {c : Configuration M} {log : BitString} {word : List O}
    (recorded : M.ExecutionTranscript data bits c log (.accepted word)) :
    M.AcceptingTranscript data (M.resetRandom c) log word := by
  generalize resultEq : Outcome.accepted word = result at recorded
  induction recorded with
  | halt c outcome terminal =>
      subst outcome
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
      | accept =>
          have same : c.output = word := by simpa [observe, action] using terminal
          rw [← same]
          exact .accept _ [] action
      | reject => simp [observe, action] at terminal
      | step state write work input auxiliary index emit => simp [observe, action] at terminal
      | readRandom no yes =>
          simp only [observe, action] at terminal
          split_ifs at terminal
          cases terminal
  | step c tail outcome state write work input auxiliary index emit action rest ih =>
      apply AcceptingTranscript.step (M.resetRandom c) false tail word state write work input auxiliary index emit action
      simpa only [resetRandom, stepConfiguration] using ih resultEq
  | random c bit tail outcome no yes action lookup rest ih =>
      exact .random _ bit tail word no yes action (ih resultEq)

end ComplexityOfGenerators.Machine
