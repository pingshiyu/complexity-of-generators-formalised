import ComplexityOfGenerators.Foundations.SpaceBounds

/-!
# Reading nondeterministic choices from a certificate

This compiler retains the native state and work alphabets. It replaces each
random read by a deterministic read and right move on the auxiliary tape, and
turns exhaustion into explicit rejection. Each source transition still costs
one transition. The source's auxiliary tape is empty, as in `NP` recognition.
-/

namespace ComplexityOfGenerators.Simulation

variable {α O : Type} (M : Machine α Bool O)

def certificateVerifier : Machine α Bool O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  states := M.states
  symbols := M.symbols
  initial := M.initial
  transition := fun q input auxiliary index work =>
    match M.transition q input none index work with
    | .accept => .accept
    | .reject => .reject
    | .readRandom no yes => match auxiliary with
      | none => .reject
      | some bit => .step (if bit then yes else no) none .stay .stay .right .stay none
    | .step next write work input _ index emit => .step next write work input .stay index emit

def certificateConfiguration (c : Configuration M) : Configuration (certificateVerifier M) where
  state := c.state
  inputHead := c.inputHead
  auxiliaryHead := c.randomHead
  indexHead := c.indexHead
  randomHead := 0
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := c.output

def certificateOutcome : Outcome O → Outcome O
  | .exhausted => .rejected
  | result => result

def certificateResult : RunState M → RunState (certificateVerifier M)
  | .running c => .running (certificateConfiguration M c)
  | .halted result => .halted (certificateOutcome result)

theorem certificateVerifier_deterministic : (certificateVerifier M).Deterministic := by
  intro q input auxiliary index work
  dsimp only [certificateVerifier]
  cases M.transition q input none index work <;> simp only
  cases auxiliary <;> trivial

theorem certificateVerifier_observe (word : List α) (certificate bits : BitString)
    (c : Configuration M) :
    (certificateVerifier M).observe (verifierData word certificate) bits (certificateConfiguration M c) =
      certificateResult M (M.observe (decisionData word) certificate c) := by
  unfold Machine.observe certificateVerifier certificateConfiguration verifierData decisionData
  simp only [List.getElem?_nil]
  cases action : M.transition c.state word[c.inputHead]? none
      (if c.indexHead < 0 then some true else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | step state write work input auxiliary index emit => rfl
  | readRandom no yes =>
      cases lookup : certificate[c.randomHead]? with
      | none =>
          have length := List.getElem?_eq_none_iff.mp lookup
          simp [certificateResult, certificateOutcome, show ¬c.randomHead < certificate.length by omega]
          rfl
      | some bit =>
          have length := List.getElem?_eq_some_iff.mp lookup
          simp [certificateResult, certificateConfiguration, length.1]
          rfl

theorem certificateVerifier_next (word : List α) (certificate bits : BitString)
    (c : Configuration M) (inputBound : c.inputHead ≤ word.length) (indexBound : c.indexHead = 0)
    (randomBound : c.randomHead ≤ certificate.length) (head : c.workHead ∈ c.visited) :
    (certificateVerifier M).next (verifierData word certificate) bits (certificateConfiguration M c) =
      certificateResult M (M.next (decisionData word) certificate c) := by
  unfold Machine.next certificateVerifier certificateConfiguration verifierData decisionData
  simp only [List.getElem?_nil]
  cases action : M.transition c.state word[c.inputHead]? none
      (if c.indexHead < 0 then some true else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | step state write work input auxiliary index emit =>
      simp [certificateResult, certificateConfiguration, Move.onInput, Nat.min_eq_left randomBound]
      cases write <;> cases emit <;> rfl
  | readRandom no yes =>
      cases lookup : certificate[c.randomHead]? with
      | none => rfl
      | some bit =>
          have length := (List.getElem?_eq_some_iff.mp lookup).1
          simp [certificateResult, certificateConfiguration, Move.onInt, Move.onInput,
            Nat.min_eq_left inputBound, Nat.min_eq_left (show c.randomHead + 1 ≤ certificate.length by omega),
            indexBound, Finset.insert_eq_of_mem head]
          rfl

private theorem next_randomHead_le (word : List α) (certificate : BitString)
    (c d : Configuration M) (bound : c.randomHead ≤ certificate.length)
    (step : M.next (decisionData word) certificate c = .running d) :
    d.randomHead ≤ certificate.length := by
  unfold Machine.next at step
  cases action : M.transition c.state (decisionData word).input[c.inputHead]?
      (decisionData word).auxiliary[c.auxiliaryHead]?
      (if c.indexHead < (decisionData word).index then some true else none) (c.work c.workHead) with
  | accept => simp [action] at step
  | reject => simp [action] at step
  | step state write work input auxiliary index emit =>
      simp only [action, RunState.running.injEq] at step
      subst d
      exact bound
  | readRandom no yes =>
      cases lookup : certificate[c.randomHead]? with
      | none => simp [action, lookup] at step
      | some bit =>
          simp only [action, lookup, RunState.running.injEq] at step
          subst d
          have := (List.getElem?_eq_some_iff.mp lookup).1
          change c.randomHead + 1 ≤ certificate.length
          omega

theorem certificateVerifier_run (word : List α) (certificate bits : BitString) (t : ℕ) :
    (certificateVerifier M).run (verifierData word certificate) bits t =
      certificateResult M (M.run (decisionData word) certificate t) := by
  have invariant : ∀ t c, M.run (decisionData word) certificate t = .running c →
      c.randomHead ≤ certificate.length := by
    intro t
    induction t with
    | zero =>
        intro c execution
        have same := M.observe_running_eq _ _ _ _ execution
        simp [same, Machine.initialConfiguration]
    | succ t ih =>
        intro c execution
        simp only [Machine.run] at execution
        cases previous : M.run (decisionData word) certificate t with
        | halted result => simp [previous] at execution
        | running current =>
            simp only [previous] at execution
            cases step : M.next (decisionData word) certificate current with
            | halted result => simp [step] at execution
            | running next =>
                simp only [step] at execution
                have same := M.observe_running_eq _ _ _ _ execution
                rw [same]
                exact next_randomHead_le M word certificate current next (ih current previous) step
  induction t with
  | zero => exact certificateVerifier_observe M word certificate bits M.initialConfiguration
  | succ t ih =>
      rw [Machine.run, ih]
      cases previous : M.run (decisionData word) certificate t with
      | halted result => simp [certificateResult, Machine.run, previous]
      | running c =>
          have bound := M.run_configurationBound (decisionData word) certificate t c previous
          have geometry := M.run_geometry (decisionData word) certificate t c previous
          have next := certificateVerifier_next M word certificate bits c bound.inputHead
            (by have := bound.indexHead; change c.indexHead ≤ 0 at this; omega)
            (invariant t c previous) geometry.head
          simp only [certificateResult]
          rw [next, Machine.run, previous]
          dsimp only
          cases step : M.next (decisionData word) certificate c with
          | halted result => rfl
          | running d => exact certificateVerifier_observe M word certificate bits d

theorem certificateVerifier_timeBound (word : List α) (certificate : BitString) (t : ℕ)
    (time : M.HaltsWithin (decisionData word) certificate t) :
    (certificateVerifier M).TimeBound (verifierData word certificate) t := by
  obtain ⟨result, execution⟩ := time
  intro bits
  exact ⟨certificateOutcome result, by rw [certificateVerifier_run, execution]; rfl⟩

theorem certificateVerifier_accepts (word : List α) (certificate bits : BitString) :
    (certificateVerifier M).Accepts (verifierData word certificate) bits ↔
      M.Accepts (decisionData word) certificate := by
  constructor
  · rintro ⟨output, t, execution⟩
    rw [certificateVerifier_run] at execution
    cases source : M.run (decisionData word) certificate t with
    | running c => simp [source, certificateResult] at execution
    | halted result =>
        cases result with
        | rejected => simp [source, certificateResult, certificateOutcome] at execution
        | exhausted => simp [source, certificateResult, certificateOutcome] at execution
        | accepted produced => exact ⟨produced, t, source⟩
  · rintro ⟨output, t, execution⟩
    exact ⟨output, t, by rw [certificateVerifier_run, execution]; rfl⟩

end ComplexityOfGenerators.Simulation
