import ComplexityOfGenerators.Foundations.RandomTape

/-!
# Primitive-transition bounds on native executions

Every transition visits at most one new cell, moves the work head by at most
one, and consumes or emits at most one symbol. These concrete invariants give
the finite tape segments and random prefixes needed by polynomial simulations.
They also account for a cell entered immediately before halting.
-/

namespace ComplexityOfGenerators

theorem Move.onInput_le (move : Move) (bound i : ℕ) (h : i ≤ bound) :
    move.onInput bound i ≤ bound := by
  cases move <;> simp only [Move.onInput] <;> omega

namespace Machine

variable {I A O : Type} (M : Machine I A O)

structure ConfigurationBound (data : InputData I A) (t : ℕ) (c : Configuration M) : Prop where
  inputHead : c.inputHead ≤ data.input.length
  auxiliaryHead : c.auxiliaryHead ≤ data.auxiliary.length
  indexHead : c.indexHead ≤ data.index
  randomHead : c.randomHead ≤ t
  workHeadLower : -(t : ℤ) ≤ c.workHead
  workHeadUpper : c.workHead ≤ (t : ℤ)
  visited : c.visited.card ≤ t + 1
  output : c.output.length ≤ t

theorem ConfigurationBound.mono {data : InputData I A} {s t : ℕ} {c : Configuration M}
    (h : M.ConfigurationBound data s c) (le : s ≤ t) : M.ConfigurationBound data t c := by
  rcases h with ⟨hi, ha, hn, hr, hl, hu, hv, ho⟩
  exact ⟨hi, ha, hn, by omega, by omega, by omega, by omega, by omega⟩

theorem initialConfiguration_bound (data : InputData I A) :
    M.ConfigurationBound data 0 M.initialConfiguration := by
  constructor <;> simp [initialConfiguration]

/-- Terminal outcomes retain the output-length bound; exhaustion records that
the run has reached the end of its finite random tape within the time budget. -/
def ExecutionBound (data : InputData I A) (bits : BitString) (t : ℕ) : RunState M → Prop
  | .running c => M.ConfigurationBound data t c
  | .halted (.accepted word) => word.length ≤ t
  | .halted .exhausted => bits.length ≤ t
  | .halted .rejected => True

theorem ExecutionBound.mono {data : InputData I A} {bits : BitString} {s t : ℕ} {r : RunState M}
    (h : M.ExecutionBound data bits s r) (le : s ≤ t) : M.ExecutionBound data bits t r := by
  cases r with
  | running c => exact ConfigurationBound.mono M h le
  | halted outcome => cases outcome <;> simp_all [ExecutionBound] <;> omega

theorem observe_executionBound (data : InputData I A) (bits : BitString) (t : ℕ)
    (c : Configuration M) (h : M.ConfigurationBound data t c) :
    M.ExecutionBound data bits t (M.observe data bits c) := by
  unfold observe
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => exact h.output
  | reject => trivial
  | step next write work input auxiliary index emit => exact h
  | readRandom no yes =>
      split_ifs with available
      · exact h
      · change bits.length ≤ t
        have := h.randomHead
        omega

theorem stepConfiguration_bound (data : InputData I A) (t : ℕ) (c : Configuration M)
    (h : M.ConfigurationBound data t c) (state : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O) :
    M.ConfigurationBound data (t + 1)
      (M.stepConfiguration data c state write work input auxiliary index emit) := by
  refine ⟨input.onInput_le _ _ h.inputHead, auxiliary.onInput_le _ _ h.auxiliaryHead,
    index.onInput_le _ _ h.indexHead, ?_, ?_, ?_, ?_, ?_⟩
  · exact h.randomHead.trans (Nat.le_succ t)
  · have := h.workHeadLower
    cases work <;> simp only [stepConfiguration, Move.onInt] <;> omega
  · have := h.workHeadUpper
    cases work <;> simp only [stepConfiguration, Move.onInt] <;> omega
  · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right h.visited 1)
  · have := h.output
    cases emit <;> simp only [stepConfiguration, List.length_append, List.length_singleton] <;> omega

theorem next_executionBound (data : InputData I A) (bits : BitString) (t : ℕ)
    (c : Configuration M) (h : M.ConfigurationBound data t c) :
    M.ExecutionBound data bits (t + 1) (M.next data bits c) := by
  unfold next
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => exact h.output.trans (Nat.le_succ t)
  | reject => trivial
  | step state write work input auxiliary index emit =>
      exact M.stepConfiguration_bound data t c h state write work input auxiliary index emit
  | readRandom no yes =>
      cases read : bits[c.randomHead]? with
      | none =>
          have endOfTape : bits.length ≤ c.randomHead := List.getElem?_eq_none_iff.mp read
          exact endOfTape.trans (h.randomHead.trans (Nat.le_succ t))
      | some bit =>
          rcases h with ⟨hi, ha, hn, hr, hl, hu, hv, ho⟩
          exact ⟨hi, ha, hn, by simpa using Nat.add_le_add_right hr 1,
            by simpa using (show -((t + 1 : ℕ) : ℤ) ≤ c.workHead by omega),
            by simpa using (show c.workHead ≤ ((t + 1 : ℕ) : ℤ) by omega),
            by simpa using (show c.visited.card ≤ t + 1 + 1 by omega),
            by simpa using (show c.output.length ≤ t + 1 by omega)⟩

/-- Bounds for every prefix of every finite-random-tape computation. -/
theorem run_executionBound (data : InputData I A) (bits : BitString) (t : ℕ) :
    M.ExecutionBound data bits t (M.run data bits t) := by
  induction t with
  | zero => exact M.observe_executionBound data bits 0 _ (M.initialConfiguration_bound data)
  | succ t ih =>
      rw [run]
      cases previous : M.run data bits t with
      | halted result =>
          rw [previous] at ih
          exact ih.mono M (Nat.le_succ t)
      | running c =>
          rw [previous] at ih
          simp only
          have nextBound := M.next_executionBound data bits t c ih
          cases next : M.next data bits c with
          | halted result => simpa only [next] using nextBound
          | running d =>
              rw [next] at nextBound
              exact M.observe_executionBound data bits (t + 1) d nextBound

theorem run_configurationBound (data : InputData I A) (bits : BitString) (t : ℕ)
    (c : Configuration M) (execution : M.run data bits t = .running c) :
    M.ConfigurationBound data t c := by
  simpa only [execution, ExecutionBound] using M.run_executionBound data bits t

theorem accepted_output_length_le (data : InputData I A) (bits : BitString) (t : ℕ)
    (word : List O) (execution : M.run data bits t = .halted (.accepted word)) :
    word.length ≤ t := by
  simpa only [execution, ExecutionBound] using M.run_executionBound data bits t

/-- A tape longer than the transition budget cannot have been exhausted. -/
theorem run_not_exhausted_of_length (data : InputData I A) (bits : BitString) (t : ℕ)
    (long : t < bits.length) : M.run data bits t ≠ .halted .exhausted := by
  intro exhausted
  have bound := M.run_executionBound data bits t
  rw [exhausted] at bound
  exact Nat.not_le_of_lt long bound

theorem ConfigurationBound.workHead_natAbs {data : InputData I A} {t : ℕ} {c : Configuration M}
    (h : M.ConfigurationBound data t c) : c.workHead.natAbs ≤ t := by
  have lower := h.workHeadLower
  have upper := h.workHeadUpper
  cases head : c.workHead <;> simp_all
  all_goals omega

/-- A live observation guarantees an actual next configuration, including when
the next instruction requests a random bit. -/
theorem next_running_of_observe_running (data : InputData I A) (bits : BitString) (c : Configuration M)
    (live : M.observe data bits c = .running c) : ∃ d, M.next data bits c = .running d := by
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => simp [observe, action] at live
  | reject => simp [observe, action] at live
  | step state write work input auxiliary index emit =>
      exact ⟨_, M.next_step data bits c state write work input auxiliary index emit action⟩
  | readRandom no yes =>
      have available : c.randomHead < bits.length := by
        by_contra absent
        simp [observe, action, absent] at live
      cases read : bits[c.randomHead]? with
      | none => have := List.getElem?_eq_none_iff.mp read; omega
      | some bit =>
          exact ⟨{c with state := if bit then yes else no, randomHead := c.randomHead + 1},
            by simp only [next, action, read]⟩

theorem runFrom_halted_add (data : InputData I A) (bits : BitString) (c : Configuration M)
    (t : ℕ) (result : Outcome O) (halted : M.runFrom data bits c t = .halted result) (extra : ℕ) :
    M.runFrom data bits c (t + extra) = .halted result := by
  induction extra with
  | zero => exact halted
  | succ extra ih =>
      change M.runFrom data bits c ((t + extra) + 1) = _
      rw [runFrom, ih]

theorem deterministic_running_randomHead (deterministic : M.Deterministic)
    (data : InputData I A) (bits : BitString) (t : ℕ) (c : Configuration M)
    (execution : M.run data bits t = .running c) : c.randomHead = 0 := by
  have preserve : ∀ c d : Configuration M, M.next data bits c = .running d → d.randomHead = c.randomHead := by
    intro c d step
    have nonrandom := deterministic c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead)
    cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
    | accept => simp [next, action] at step
    | reject => simp [next, action] at step
    | readRandom no yes => simp [action] at nonrandom
    | step state write work input auxiliary index emit =>
        simp only [next, action] at step
        have same := RunState.running.inj step
        subst d
        rfl
  induction t generalizing c with
  | zero =>
      have same := M.observe_running_eq data bits M.initialConfiguration c execution
      rw [same]
      rfl
  | succ t ih =>
      simp only [run] at execution
      cases previous : M.run data bits t with
      | halted result => simp [previous] at execution
      | running current =>
          simp only [previous] at execution
          cases step : M.next data bits current with
          | halted result => simp [step] at execution
          | running next =>
              simp only [step] at execution
              have same := M.observe_running_eq data bits next c execution
              rw [same, preserve current next step]
              exact ih current previous

end Machine

end ComplexityOfGenerators
