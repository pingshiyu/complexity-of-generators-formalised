import ComplexityOfGenerators.Foundations.ExecutionBounds

/-! A native decider reading its word from the auxiliary tape. Its ordinary
input and family-index tapes are ignored; decision output is discarded. -/

namespace ComplexityOfGenerators.Simulation

set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Unit)

def auxiliaryDecision : Machine Unit Bool Bool where
  inputFinite := M.outputFinite
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition := fun q _ auxiliary _ work =>
    match M.transition q auxiliary none none work with
    | .accept => .accept
    | .reject => .reject
    | .readRandom no yes => .readRandom no yes
    | .step next write work input _ _ _ =>
        .step next write work .stay input .stay none

def auxiliaryDecisionConfiguration (c : Configuration M) : Configuration (auxiliaryDecision M) where
  state := c.state
  inputHead := 0
  auxiliaryHead := c.inputHead
  indexHead := 0
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := []

def auxiliaryDecisionOutcome : Outcome Unit → Outcome Bool
  | .accepted _ => .accepted []
  | .rejected => .rejected
  | .exhausted => .exhausted

def auxiliaryDecisionResult : RunState M → RunState (auxiliaryDecision M)
  | .running c => .running (auxiliaryDecisionConfiguration M c)
  | .halted result => .halted (auxiliaryDecisionOutcome result)

theorem auxiliaryDecision_observe (n : ℕ) (word bits : BitString) (c : Configuration M) :
    (auxiliaryDecision M).observe (generatorData n word) bits (auxiliaryDecisionConfiguration M c) =
      auxiliaryDecisionResult M (M.observe (decisionData word) bits c) := by
  simp only [Machine.observe, auxiliaryDecision, auxiliaryDecisionConfiguration,
    generatorData, decisionData, List.getElem?_nil, Nat.not_lt_zero, ↓reduceIte]
  cases M.transition c.state word[c.inputHead]? none none (c.work c.workHead) <;>
    simp only [auxiliaryDecisionResult, auxiliaryDecisionOutcome, auxiliaryDecisionConfiguration]
  split_ifs <;> rfl

theorem auxiliaryDecision_next (n : ℕ) (word bits : BitString) (c : Configuration M) :
    (auxiliaryDecision M).next (generatorData n word) bits (auxiliaryDecisionConfiguration M c) =
      auxiliaryDecisionResult M (M.next (decisionData word) bits c) := by
  simp only [Machine.next, auxiliaryDecision, auxiliaryDecisionConfiguration,
    generatorData, decisionData, List.getElem?_nil, Nat.not_lt_zero, ↓reduceIte]
  cases M.transition c.state word[c.inputHead]? none none (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes => cases bits[c.randomHead]? <;> rfl
  | step state write work input auxiliary index emit =>
      cases write <;> cases emit <;> simp [auxiliaryDecisionResult, auxiliaryDecisionConfiguration, Move.onInput]

theorem auxiliaryDecision_run (n : ℕ) (word bits : BitString) (t : ℕ) :
    (auxiliaryDecision M).run (generatorData n word) bits t =
      auxiliaryDecisionResult M (M.run (decisionData word) bits t) := by
  induction t with
  | zero => exact auxiliaryDecision_observe M n word bits M.initialConfiguration
  | succ t ih =>
      rw [Machine.run, ih, Machine.run]
      cases M.run (decisionData word) bits t with
      | halted result => rfl
      | running c =>
          simp only [auxiliaryDecisionResult]
          rw [auxiliaryDecision_next]
          cases M.next (decisionData word) bits c with
          | halted result => rfl
          | running d => exact auxiliaryDecision_observe M n word bits d

theorem auxiliaryDecision_timeBound (n : ℕ) (word : BitString) (t : ℕ)
    (bound : M.TimeBound (decisionData word) t) :
    (auxiliaryDecision M).TimeBound (generatorData n word) t := by
  intro bits
  obtain ⟨result, halted⟩ := bound bits
  exact ⟨auxiliaryDecisionOutcome result, by rw [auxiliaryDecision_run, halted]; rfl⟩

theorem auxiliaryDecision_accepts (n : ℕ) (word bits : BitString) :
    (auxiliaryDecision M).Accepts (generatorData n word) bits ↔ M.Accepts (decisionData word) bits := by
  constructor
  · rintro ⟨out, t, accepted⟩
    rw [auxiliaryDecision_run] at accepted
    cases source : M.run (decisionData word) bits t with
    | running c => simp [source, auxiliaryDecisionResult] at accepted
    | halted result =>
        cases result with
        | accepted out => exact ⟨out, t, source⟩
        | rejected => simp [source, auxiliaryDecisionResult, auxiliaryDecisionOutcome] at accepted
        | exhausted => simp [source, auxiliaryDecisionResult, auxiliaryDecisionOutcome] at accepted
  · rintro ⟨out, t, accepted⟩
    exact ⟨[], t, by rw [auxiliaryDecision_run, accepted]; rfl⟩

end ComplexityOfGenerators.Simulation
