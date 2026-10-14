import ComplexityOfGenerators.Foundations.RandomTape
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Sum

/-!
# Sequential composition on a shared work tape

A finite routine has the same primitive instructions as a native machine. It
can be attached to a computation without clearing its work tape. Acceptance of
the first computation transfers control to the routine in one native step;
the routine's accepting output is the output of the combined machine.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

structure Routine (I A O : Type) (symbols : ℕ) where
  states : ℕ
  initial : Fin states
  transition : Fin states → Option I → Option A → Option Unit → Option (Fin symbols) →
    Instruction O states symbols

def Routine.machine {I A O : Type} [Finite I] [Finite A] [Finite O]
    {symbols : ℕ} (routine : Routine I A O symbols) : Machine I A O where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := routine.states
  symbols := symbols
  initial := routine.initial
  transition := routine.transition

variable {I A O : Type} [Finite O]
variable (M : Machine I A Unit) (routine : Routine I A O M.symbols)

def sequenceControl : (Fin M.states ⊕ Fin routine.states) ≃
    Fin (Fintype.card (Fin M.states ⊕ Fin routine.states)) := Fintype.equivFin _

def sequenceLeftInstruction : Instruction Unit M.states M.symbols →
    Instruction O (Fintype.card (Fin M.states ⊕ Fin routine.states)) M.symbols
  | .accept => .step (sequenceControl M routine (.inr routine.initial)) none .stay .stay .stay .stay none
  | .reject => .reject
  | .readRandom no yes => .readRandom (sequenceControl M routine (.inl no))
      (sequenceControl M routine (.inl yes))
  | .step next write work input auxiliary index _ =>
      .step (sequenceControl M routine (.inl next)) write work input auxiliary index none

def sequenceRightInstruction : Instruction O routine.states M.symbols →
    Instruction O (Fintype.card (Fin M.states ⊕ Fin routine.states)) M.symbols
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (sequenceControl M routine (.inr no))
      (sequenceControl M routine (.inr yes))
  | .step next write work input auxiliary index emit =>
      .step (sequenceControl M routine (.inr next)) write work input auxiliary index emit

def sequenceMachine : Machine I A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := inferInstance
  states := Fintype.card (Fin M.states ⊕ Fin routine.states)
  symbols := M.symbols
  initial := sequenceControl M routine (.inl M.initial)
  transition := fun q input auxiliary index work => match (sequenceControl M routine).symm q with
    | .inl q => sequenceLeftInstruction M routine (M.transition q input auxiliary index work)
    | .inr q => sequenceRightInstruction M routine (routine.transition q input auxiliary index work)

def sequenceLeftConfiguration (c : Configuration M) (out : List O) :
    Configuration (sequenceMachine M routine) where
  state := sequenceControl M routine (.inl c.state)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := out

theorem sequence_left_observe (data : InputData I A) (bits : BitString)
    (c : Configuration M) (out : List O)
    (live : M.observe data bits c = .running c) :
    (sequenceMachine M routine).observe data bits (sequenceLeftConfiguration M routine c out) =
      .running (sequenceLeftConfiguration M routine c out) := by
  unfold Machine.observe at live
  simp only [Machine.observe, sequenceMachine, sequenceLeftConfiguration, Equiv.symm_apply_apply]
  cases h : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => simp [h] at live
  | reject => simp [h] at live
  | readRandom no yes =>
      simp only [h] at live
      split_ifs at live with available
      · simp [sequenceLeftInstruction, available]
  | step next write work input auxiliary index emit => rfl

theorem sequence_left_next (data : InputData I A) (bits : BitString)
    (c d : Configuration M) (out : List O)
    (step : M.next data bits c = .running d) :
    (sequenceMachine M routine).next data bits (sequenceLeftConfiguration M routine c out) =
      .running (sequenceLeftConfiguration M routine d out) := by
  unfold Machine.next at step
  simp only [Machine.next, sequenceMachine, sequenceLeftConfiguration, Equiv.symm_apply_apply]
  cases h : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => simp [h] at step
  | reject => simp [h] at step
  | readRandom no yes =>
      simp only [h] at step
      cases bit : bits[c.randomHead]? with
      | none => simp [bit] at step
      | some value =>
          simp only [bit, RunState.running.injEq] at step
          subst d
          cases value <;> simp [sequenceLeftInstruction]
  | step next write work input auxiliary index emit =>
      simp only [h, RunState.running.injEq] at step
      subst d
      cases write <;> cases emit <;> rfl

variable [Finite I] [Finite A]

def sequenceRightConfiguration (c : Configuration routine.machine) :
    Configuration (sequenceMachine M routine) where
  state := sequenceControl M routine (.inr c.state)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

def sequenceRightResult : RunState routine.machine → RunState (sequenceMachine M routine)
  | .running c => .running (sequenceRightConfiguration M routine c)
  | .halted result => .halted result

theorem sequence_right_observe (data : InputData I A) (bits : BitString)
    (c : Configuration routine.machine) :
    (sequenceMachine M routine).observe data bits (sequenceRightConfiguration M routine c) =
      sequenceRightResult M routine (routine.machine.observe data bits c) := by
  simp only [Machine.observe, sequenceMachine, sequenceRightConfiguration,
    Equiv.symm_apply_apply, Routine.machine]
  cases routine.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work c.workHead) <;>
    simp only [sequenceRightInstruction, sequenceRightResult, sequenceRightConfiguration]
  split_ifs <;> rfl

theorem sequence_right_next (data : InputData I A) (bits : BitString)
    (c : Configuration routine.machine) :
    (sequenceMachine M routine).next data bits (sequenceRightConfiguration M routine c) =
      sequenceRightResult M routine (routine.machine.next data bits c) := by
  simp only [Machine.next, sequenceMachine, sequenceRightConfiguration,
    Equiv.symm_apply_apply, Routine.machine]
  cases routine.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work c.workHead) <;>
    simp only [sequenceRightInstruction, sequenceRightResult, sequenceRightConfiguration]
  · cases bits[c.randomHead]? with
    | none => rfl
    | some bit => cases bit <;> rfl
  · rename_i next write work input auxiliary index emit
    cases write <;> cases emit <;> rfl

theorem sequence_right_runFrom (data : InputData I A) (bits : BitString)
    (c : Configuration routine.machine) (t : ℕ) :
    (sequenceMachine M routine).runFrom data bits (sequenceRightConfiguration M routine c) t =
      sequenceRightResult M routine (routine.machine.runFrom data bits c t) := by
  induction t with
  | zero => exact sequence_right_observe M routine data bits c
  | succ t ih =>
      simp only [Machine.runFrom, ih]
      cases routine.machine.runFrom data bits c t with
      | halted result => rfl
      | running d =>
          simp only [sequenceRightResult, sequence_right_next]
          cases routine.machine.next data bits d with
          | halted result => rfl
          | running next => exact sequence_right_observe M routine data bits next

/-- The ordinary `stay` instruction still applies the model's readonly-head
clamping and visited-cell accounting. The work tape and random position persist. -/
def handoffConfiguration (data : InputData I A) (c : Configuration M) (out : List O) :
    Configuration routine.machine where
  state := routine.initial
  inputHead := Move.stay.onInput data.input.length c.inputHead
  auxiliaryHead := Move.stay.onInput data.auxiliary.length c.auxiliaryHead
  indexHead := Move.stay.onInput data.index c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := insert c.workHead c.visited
  output := out

theorem sequence_accept_handoff (data : InputData I A) (bits : BitString)
    (c : Configuration M) (out : List O)
    (accepted : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) = .accept) :
    (sequenceMachine M routine).runFrom data bits (sequenceLeftConfiguration M routine c out) 1 =
      (sequenceMachine M routine).observe data bits
        (sequenceRightConfiguration M routine (handoffConfiguration M routine data c out)) := by
  let combined := sequenceMachine M routine
  let start := sequenceLeftConfiguration M routine c out
  let finish := sequenceRightConfiguration M routine (handoffConfiguration M routine data c out)
  have table : combined.transition start.state data.input[start.inputHead]?
      data.auxiliary[start.auxiliaryHead]? (if start.indexHead < data.index then some () else none)
      (start.work start.workHead) =
      .step (sequenceControl M routine (.inr routine.initial)) none .stay .stay .stay .stay none := by
    simp [combined, start, sequenceMachine, sequenceLeftConfiguration, accepted, sequenceLeftInstruction]
  have live := combined.observe_step data bits start _ _ _ _ _ _ _ table
  have step : combined.next data bits start = .running finish := by
    simpa [combined, start, finish, Machine.stepConfiguration, sequenceLeftConfiguration,
      sequenceRightConfiguration, handoffConfiguration, Move.onInt] using
      combined.next_step data bits start _ _ _ _ _ _ _ table
  exact combined.runFrom_shift data bits start finish live step 0

end

end ComplexityOfGenerators.Simulation
