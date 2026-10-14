import ComplexityOfGenerators.Foundations.ExecutionBounds
import Mathlib.Data.Fintype.EquivFin

/-!
# Complementing a native deterministic decider

Acceptance and rejection are exchanged, and irrelevant output is discarded.
The construction costs no additional steps or work cells. Exhaustion is kept
separate; the complement theorem below rules it out using determinism, rather
than interpreting an exhausted nondeterministic branch as rejection.
-/

namespace ComplexityOfGenerators.Simulation

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

def decisionComplement : Machine I A Unit where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := inferInstance
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition := fun q input auxiliary index work =>
    match M.transition q input auxiliary index work with
    | .accept => .reject
    | .reject => .accept
    | .readRandom no yes => .readRandom no yes
    | .step next write work input auxiliary index _ =>
        .step next write work input auxiliary index none

def complementConfiguration (c : Configuration M) : Configuration (decisionComplement M) where
  state := c.state
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := []

def complementOutcome : Outcome O → Outcome Unit
  | .accepted _ => .rejected
  | .rejected => .accepted []
  | .exhausted => .exhausted

def complementResult : RunState M → RunState (decisionComplement M)
  | .running c => .running (complementConfiguration M c)
  | .halted result => .halted (complementOutcome result)

theorem decisionComplement_observe (data : InputData I A) (bits : BitString) (c : Configuration M) :
    (decisionComplement M).observe data bits (complementConfiguration M c) =
      complementResult M (M.observe data bits c) := by
  simp only [Machine.observe, decisionComplement, complementConfiguration]
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) <;>
    simp only [action, complementResult, complementOutcome, complementConfiguration]
  split_ifs <;> rfl

theorem decisionComplement_next (data : InputData I A) (bits : BitString) (c : Configuration M) :
    (decisionComplement M).next data bits (complementConfiguration M c) =
      complementResult M (M.next data bits c) := by
  simp only [Machine.next, decisionComplement, complementConfiguration]
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes => cases bits[c.randomHead]? <;> rfl
  | step state write work input auxiliary index emit => cases write <;> cases emit <;> rfl

theorem decisionComplement_run (data : InputData I A) (bits : BitString) (t : ℕ) :
    (decisionComplement M).run data bits t = complementResult M (M.run data bits t) := by
  induction t with
  | zero => exact decisionComplement_observe M data bits M.initialConfiguration
  | succ t ih =>
      rw [Machine.run, ih, Machine.run]
      cases M.run data bits t with
      | halted result => rfl
      | running c =>
          simp only [complementResult]
          rw [decisionComplement_next]
          cases M.next data bits c with
          | halted result => rfl
          | running d => exact decisionComplement_observe M data bits d

theorem decisionComplement_deterministic (deterministic : M.Deterministic) :
    (decisionComplement M).Deterministic := by
  intro q input auxiliary index work
  have source := deterministic q input auxiliary index work
  unfold decisionComplement
  cases action : M.transition q input auxiliary index work <;> simp_all

theorem decisionComplement_timeBound (data : InputData I A) (t : ℕ) (time : M.TimeBound data t) :
    (decisionComplement M).TimeBound data t := by
  intro bits
  obtain ⟨result, halted⟩ := time bits
  exact ⟨complementOutcome result, by rw [decisionComplement_run, halted]; rfl⟩

theorem decisionComplement_accepts_iff_rejected (data : InputData I A) (bits : BitString) :
    (decisionComplement M).Accepts data bits ↔ ∃ t, M.run data bits t = .halted .rejected := by
  constructor
  · rintro ⟨word, t, accepted⟩
    rw [decisionComplement_run] at accepted
    cases source : M.run data bits t with
    | running c => simp [source, complementResult] at accepted
    | halted result =>
        cases result with
        | accepted out => simp [source, complementResult, complementOutcome] at accepted
        | rejected => exact ⟨t, source⟩
        | exhausted => simp [source, complementResult, complementOutcome] at accepted
  · rintro ⟨t, rejected⟩
    exact ⟨[], t, by rw [decisionComplement_run, rejected]; rfl⟩

theorem decisionComplement_accepts_iff (deterministic : M.Deterministic) (data : InputData I A)
    (halts : M.Halts data []) :
    (decisionComplement M).Accepts data [] ↔ ¬ M.Accepts data [] := by
  rw [decisionComplement_accepts_iff_rejected]
  constructor
  · rintro ⟨t, rejected⟩ ⟨word, s, accepted⟩
    have impossible := M.halted_outcome_unique data [] t s _ _ rejected accepted
    cases impossible
  · intro absent
    obtain ⟨t, result, halted⟩ := halts
    cases result with
    | accepted word => exact False.elim (absent ⟨word, t, halted⟩)
    | rejected => exact ⟨t, halted⟩
    | exhausted =>
        let long := List.replicate (t + 1) false
        have same := M.deterministic_run deterministic data long [] t
        rw [halted] at same
        exact False.elim (M.run_not_exhausted_of_length data long t (by simp [long]) same)

end ComplexityOfGenerators.Simulation
