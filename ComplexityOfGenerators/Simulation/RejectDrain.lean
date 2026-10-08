import ComplexityOfGenerators.Foundations.ExecutionBounds
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Fintype.Option

/-!
# Turning explicit rejection into random-tape exhaustion

This finite-control compiler preserves every ordinary instruction. On explicit
rejection it consumes the remaining random tape. No work-tape clearing or
unbounded transition is used. It is the final step in making deterministic
certificate replay a generator, including on invalid certificates.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

def rejectDrainControl : Option (Fin M.states) ≃ Fin (Fintype.card (Option (Fin M.states))) :=
  Fintype.equivFin _

def rejectDrainInstruction : Instruction O M.states M.symbols →
    Instruction O (Fintype.card (Option (Fin M.states))) M.symbols
  | .accept => .accept
  | .reject => .readRandom (rejectDrainControl M none) (rejectDrainControl M none)
  | .readRandom no yes => .readRandom (rejectDrainControl M (some no)) (rejectDrainControl M (some yes))
  | .step next write work input auxiliary index emit =>
      .step (rejectDrainControl M (some next)) write work input auxiliary index emit

def rejectDrain : Machine I A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  states := Fintype.card (Option (Fin M.states))
  symbols := M.symbols
  initial := rejectDrainControl M (some M.initial)
  transition := fun q input auxiliary index work => match (rejectDrainControl M).symm q with
    | none => .readRandom (rejectDrainControl M none) (rejectDrainControl M none)
    | some state => rejectDrainInstruction M (M.transition state input auxiliary index work)

def rejectDrainConfiguration (c : Configuration M) : Configuration (rejectDrain M) where
  state := rejectDrainControl M (some c.state)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

def drainConfiguration (c : Configuration M) (r : ℕ) : Configuration (rejectDrain M) :=
  {rejectDrainConfiguration M c with state := rejectDrainControl M none, randomHead := r}

def rejectDrainOutcome : Outcome O → Outcome O
  | .accepted word => .accepted word
  | .rejected | .exhausted => .exhausted

theorem drain_runFrom (data : InputData I A) (bits : BitString) (c : Configuration M) (r t : ℕ) :
    (rejectDrain M).runFrom data bits (drainConfiguration M c r) t =
      if r + t < bits.length then .running (drainConfiguration M c (r + t)) else .halted .exhausted := by
  induction t with
  | zero =>
      simp [Machine.runFrom, Machine.observe, drainConfiguration, rejectDrain, rejectDrainConfiguration]
  | succ t ih =>
      rw [Machine.runFrom, ih]
      by_cases available : r + t < bits.length
      · rw [ite_eq_left available]
        have lookup := List.getElem?_eq_getElem available
        simp only [Machine.next, rejectDrain, drainConfiguration, rejectDrainConfiguration,
          Equiv.symm_apply_apply, lookup]
        cases bits[r + t] <;> simp [Machine.observe, Nat.add_assoc]
      · simp [available, show ¬r + (t + 1) < bits.length by omega]

theorem rejectDrain_observe_running (data : InputData I A) (bits : BitString) (c : Configuration M)
    (live : M.observe data bits c = .running c) :
    (rejectDrain M).observe data bits (rejectDrainConfiguration M c) =
      .running (rejectDrainConfiguration M c) := by
  unfold Machine.observe at live
  simp only [Machine.observe, rejectDrain, rejectDrainConfiguration, Equiv.symm_apply_apply]
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | accept => simp [action] at live
  | reject => simp [action] at live
  | step state write work input auxiliary index emit => simp [rejectDrainInstruction]
  | readRandom no yes =>
      have available : c.randomHead < bits.length := by
        by_contra absent
        simp [action, absent] at live
      simp [rejectDrainInstruction, available]

theorem rejectDrain_next_running (data : InputData I A) (bits : BitString) (c d : Configuration M)
    (step : M.next data bits c = .running d) :
    (rejectDrain M).next data bits (rejectDrainConfiguration M c) =
      .running (rejectDrainConfiguration M d) := by
  unfold Machine.next at step
  simp only [Machine.next, rejectDrain, rejectDrainConfiguration, Equiv.symm_apply_apply]
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | accept => simp [action] at step
  | reject => simp [action] at step
  | step state write work input auxiliary index emit =>
      simp only [action, RunState.running.injEq] at step
      subst d
      simp only [rejectDrainInstruction]
      cases write <;> cases emit <;> rfl
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [action, lookup] at step
      | some bit =>
          simp only [action, lookup, RunState.running.injEq] at step
          subst d
          cases bit <;> simp [rejectDrainInstruction]

/-- A terminal source observation is preserved, except that rejection spends
at most the finite tape length draining randomness. -/
theorem rejectDrain_terminal (data : InputData I A) (bits : BitString) (c : Configuration M)
    (result : Outcome O) (terminal : M.observe data bits c = .halted result) :
    (rejectDrain M).runFrom data bits (rejectDrainConfiguration M c) bits.length =
      .halted (rejectDrainOutcome result) := by
  unfold Machine.observe at terminal
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) with
  | accept =>
      simp only [action, RunState.halted.injEq] at terminal
      subst result
      apply Machine.runFrom_halted
      simp [Machine.observe, rejectDrain, rejectDrainConfiguration, action, rejectDrainInstruction,
        rejectDrainOutcome]
  | reject =>
      simp only [action, RunState.halted.injEq] at terminal
      subst result
      by_cases available : c.randomHead < bits.length
      · have live : (rejectDrain M).observe data bits (rejectDrainConfiguration M c) =
            .running (rejectDrainConfiguration M c) := by
          simp [Machine.observe, rejectDrain, rejectDrainConfiguration, action,
            rejectDrainInstruction, available]
        have lookup := List.getElem?_eq_getElem available
        have step : (rejectDrain M).next data bits (rejectDrainConfiguration M c) =
            .running (drainConfiguration M c (c.randomHead + 1)) := by
          simp [Machine.next, rejectDrain, rejectDrainConfiguration, action,
            rejectDrainInstruction, lookup, drainConfiguration]
        have shift := (rejectDrain M).runFrom_shift data bits _ _ live step (bits.length - 1)
        have positive : bits.length - 1 + 1 = bits.length := by omega
        rw [positive, drain_runFrom] at shift
        simpa [rejectDrainOutcome, show ¬c.randomHead + 1 + (bits.length - 1) < bits.length by omega] using shift
      · apply Machine.runFrom_halted
        simp [Machine.observe, rejectDrain, rejectDrainConfiguration, action,
          rejectDrainInstruction, available, rejectDrainOutcome]
  | step state write work input auxiliary index emit => simp [action] at terminal
  | readRandom no yes =>
      have unavailable : ¬c.randomHead < bits.length := by
        by_contra available
        simp [action, available] at terminal
      have resultEq : result = .exhausted := by simpa [action, unavailable] using terminal.symm
      subst result
      apply Machine.runFrom_halted
      simp [Machine.observe, rejectDrain, rejectDrainConfiguration, action,
        rejectDrainInstruction, unavailable, rejectDrainOutcome]

theorem rejectDrain_runFrom_halted (data : InputData I A) (bits : BitString)
    (c : Configuration M) (t : ℕ) (result : Outcome O)
    (source : M.runFrom data bits c t = .halted result) :
    (rejectDrain M).runFrom data bits (rejectDrainConfiguration M c) (t + bits.length) =
      .halted (rejectDrainOutcome result) := by
  induction t generalizing c with
  | zero => simpa using rejectDrain_terminal M data bits c result source
  | succ t ih =>
      cases observation : M.observe data bits c with
      | halted out =>
          have same := M.runFrom_halted data bits c out observation (t + 1)
          rw [source] at same
          cases same
          have terminal := rejectDrain_terminal M data bits c result observation
          simpa only [Nat.add_comm bits.length (t + 1)] using
            (rejectDrain M).runFrom_halted_add data bits _ bits.length _ terminal (t + 1)
      | running d =>
          have same := M.observe_running_eq data bits c d observation
          subst d
          obtain ⟨next, step⟩ := M.next_running_of_observe_running data bits c observation
          rw [M.runFrom_shift data bits c next observation step t] at source
          have targetLive := rejectDrain_observe_running M data bits c observation
          have targetStep := rejectDrain_next_running M data bits c next step
          have shifted := (rejectDrain M).runFrom_shift data bits _ _ targetLive targetStep (t + bits.length)
          rw [show t + 1 + bits.length = (t + bits.length) + 1 by omega, shifted]
          exact ih next source

theorem rejectDrain_run_halted (data : InputData I A) (bits : BitString) (t : ℕ) (result : Outcome O)
    (source : M.run data bits t = .halted result) :
    (rejectDrain M).run data bits (t + bits.length) = .halted (rejectDrainOutcome result) := by
  have h := rejectDrain_runFrom_halted M data bits M.initialConfiguration t result
    (by simpa only [Machine.runFrom_initial] using source)
  have initial : rejectDrainConfiguration M M.initialConfiguration = (rejectDrain M).initialConfiguration := rfl
  simpa only [initial, Machine.runFrom_initial] using h

end

end ComplexityOfGenerators.Simulation
