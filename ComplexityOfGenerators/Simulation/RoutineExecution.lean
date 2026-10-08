import ComplexityOfGenerators.Simulation.RoutineComposition

/-! Executions of the first component survive sequential composition until
acceptance transfers control. In particular, running configurations and random
tape exhaustion are preserved, including exhaustion at time zero. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite O]
variable (M : Machine I A Unit) (routine : Routine I A O M.symbols)

def SequenceLeftRelated (out : List O) (source : RunState M)
    (target : RunState (sequenceMachine M routine)) : Prop :=
  match source with
  | .running c => target = .running (sequenceLeftConfiguration M routine c out)
  | .halted (.accepted _) => True
  | .halted .rejected => target = .halted .rejected
  | .halted .exhausted => target = .halted .exhausted

theorem sequence_left_observe_related (data : InputData I A) (bits : BitString)
    (c : Configuration M) (out : List O) :
    SequenceLeftRelated M routine out (M.observe data bits c)
      ((sequenceMachine M routine).observe data bits (sequenceLeftConfiguration M routine c out)) := by
  simp only [Machine.observe, sequenceMachine, sequenceLeftConfiguration, Equiv.symm_apply_apply]
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) <;>
    simp only [sequenceLeftInstruction, SequenceLeftRelated]
  · split_ifs <;> rfl
  · rfl

theorem sequence_left_next_related (data : InputData I A) (bits : BitString)
    (c : Configuration M) (out : List O) :
    SequenceLeftRelated M routine out (M.next data bits c)
      ((sequenceMachine M routine).next data bits (sequenceLeftConfiguration M routine c out)) := by
  simp only [Machine.next, sequenceMachine, sequenceLeftConfiguration, Equiv.symm_apply_apply]
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) <;>
    simp only [sequenceLeftInstruction, SequenceLeftRelated]
  · cases bits[c.randomHead]? with
    | none => rfl
    | some bit => cases bit <;> rfl
  · rename_i next write work input auxiliary index emit
    cases write <;> cases emit <;> rfl

theorem sequence_left_runFrom_related (data : InputData I A) (bits : BitString)
    (c : Configuration M) (out : List O) (t : ℕ) :
    SequenceLeftRelated M routine out (M.runFrom data bits c t)
      ((sequenceMachine M routine).runFrom data bits (sequenceLeftConfiguration M routine c out) t) := by
  induction t with
  | zero => exact sequence_left_observe_related M routine data bits c out
  | succ t ih =>
      cases previous : M.runFrom data bits c t with
      | halted result =>
          cases result with
          | accepted word => simp [Machine.runFrom, previous, SequenceLeftRelated]
          | rejected =>
              simp only [previous, SequenceLeftRelated] at ih
              simp only [Machine.runFrom, previous, ih, SequenceLeftRelated]
          | exhausted =>
              simp only [previous, SequenceLeftRelated] at ih
              simp only [Machine.runFrom, previous, ih, SequenceLeftRelated]
      | running d =>
          simp only [previous, SequenceLeftRelated] at ih
          have next := sequence_left_next_related M routine data bits d out
          simp only [Machine.runFrom, previous, ih]
          cases step : M.next data bits d with
          | halted result =>
              cases result with
              | accepted word => trivial
              | rejected =>
                  simp only [step, SequenceLeftRelated] at next
                  simp only [next, SequenceLeftRelated]
              | exhausted =>
                  simp only [step, SequenceLeftRelated] at next
                  simp only [next, SequenceLeftRelated]
          | running e =>
              simp only [step, SequenceLeftRelated] at next
              rw [next]
              exact sequence_left_observe_related M routine data bits e out

theorem sequence_left_running (data : InputData I A) (bits : BitString)
    (c d : Configuration M) (out : List O) (t : ℕ)
    (execution : M.runFrom data bits c t = .running d) :
    (sequenceMachine M routine).runFrom data bits (sequenceLeftConfiguration M routine c out) t =
      .running (sequenceLeftConfiguration M routine d out) := by
  have related := sequence_left_runFrom_related M routine data bits c out t
  simpa only [execution, SequenceLeftRelated] using related

theorem sequence_left_exhausted (data : InputData I A) (bits : BitString)
    (c : Configuration M) (out : List O) (t : ℕ)
    (execution : M.runFrom data bits c t = .halted .exhausted) :
    (sequenceMachine M routine).runFrom data bits (sequenceLeftConfiguration M routine c out) t =
      .halted .exhausted := by
  have related := sequence_left_runFrom_related M routine data bits c out t
  simpa only [execution, SequenceLeftRelated] using related

end

end ComplexityOfGenerators.Simulation
