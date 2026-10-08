import ComplexityOfGenerators.Machine

/-!
# Read-once random tape semantics

A successful finite run cannot inspect the end of its random tape. Consequently
appending randomness preserves every non-exhausted run. These facts justify the
paper's use of finite prefixes as cylinders, and the bounded seed witnesses in
the nondeterministic-recognition and cryptographic reductions.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

/-- The configuration update of the existing primitive `step` instruction. -/
def stepConfiguration (data : InputData I A) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols))
    (workMove inputMove auxiliaryMove indexMove : Move) (emit : Option O) : Configuration M where
  state := state
  inputHead := inputMove.onInput data.input.length c.inputHead
  auxiliaryHead := auxiliaryMove.onInput data.auxiliary.length c.auxiliaryHead
  indexHead := indexMove.onInput data.index c.indexHead
  randomHead := c.randomHead
  workHead := workMove.onInt c.workHead
  work := match write with
    | none => c.work
    | some symbol => Function.update c.work c.workHead (some symbol)
  visited := insert (workMove.onInt c.workHead) c.visited
  output := match emit with
    | none => c.output
    | some symbol => c.output ++ [symbol]

theorem observe_step (data : InputData I A) (bits : BitString) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols))
    (workMove inputMove auxiliaryMove indexMove : Move) (emit : Option O)
    (instruction : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .step state write workMove inputMove auxiliaryMove indexMove emit) :
    M.observe data bits c = .running c := by simp [observe, instruction]

theorem next_step (data : InputData I A) (bits : BitString) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols))
    (workMove inputMove auxiliaryMove indexMove : Move) (emit : Option O)
    (instruction : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .step state write workMove inputMove auxiliaryMove indexMove emit) :
    M.next data bits c = .running
      (M.stepConfiguration data c state write workMove inputMove auxiliaryMove indexMove emit) := by
  simp [next, instruction, stepConfiguration]
  exact ⟨rfl, rfl⟩

/-- The existing evaluator started at an arbitrary configuration. This is used
to state simulation invariants; it does not add any machine instructions. -/
def runFrom (data : InputData I A) (bits : BitString) (start : Configuration M) :
    ℕ → RunState M
  | 0 => M.observe data bits start
  | t + 1 => match runFrom data bits start t with
    | .halted result => .halted result
    | .running c => match M.next data bits c with
      | .halted result => .halted result
      | .running c' => M.observe data bits c'

@[simp] theorem runFrom_initial (data : InputData I A) (bits : BitString) (t : ℕ) :
    M.runFrom data bits M.initialConfiguration t = M.run data bits t := by
  induction t with
  | zero => rfl
  | succ t ih =>
      simp only [runFrom, run, ih]
      rfl

/-- One verified primitive transition consumes exactly one clock tick. -/
theorem runFrom_shift (data : InputData I A) (bits : BitString)
    (c d : Configuration M)
    (observation : M.observe data bits c = .running c)
    (step : M.next data bits c = .running d) (t : ℕ) :
    M.runFrom data bits c (t + 1) = M.runFrom data bits d t := by
  induction t with
  | zero => simp only [runFrom, observation, step]
  | succ t ih =>
      rw [runFrom, ih]
      rfl

theorem runFrom_halted (data : InputData I A) (bits : BitString)
    (c : Configuration M) (result : Outcome O)
    (observation : M.observe data bits c = .halted result) (t : ℕ) :
    M.runFrom data bits c t = .halted result := by
  induction t with
  | zero => exact observation
  | succ t ih => simp only [runFrom, ih]

theorem runFrom_add (data : InputData I A) (bits : BitString)
    (c d : Configuration M) (s : ℕ)
    (simulation : M.runFrom data bits c s = M.observe data bits d) (t : ℕ) :
    M.runFrom data bits c (s + t) = M.runFrom data bits d t := by
  induction t with
  | zero => exact simulation
  | succ t ih =>
      rw [Nat.add_succ, runFrom, ih]
      rfl

theorem observe_running_eq (data : InputData I A) (bits : BitString)
    (c d : Configuration M) (h : M.observe data bits c = .running d) : d = c := by
  unfold observe at h
  split at h
  · contradiction
  · contradiction
  · split_ifs at h
    exact (RunState.running.inj h).symm
  · cases h
    rfl

theorem run_running_observe (data : InputData I A) (bits : BitString)
    (t : ℕ) (c : Configuration M) (h : M.run data bits t = .running c) :
    M.observe data bits c = .running c := by
  cases t with
  | zero =>
      change M.observe data bits M.initialConfiguration = .running c at h
      have same := M.observe_running_eq data bits M.initialConfiguration c h
      simpa [same] using h
  | succ t =>
      simp only [run] at h
      split at h
      · contradiction
      · split at h
        · contradiction
        · rename_i d _
          have same := M.observe_running_eq data bits d c h
          simpa [same] using h

theorem observe_append_of_not_exhausted (data : InputData I A)
    (bits tail : BitString) (c : Configuration M)
    (h : M.observe data bits c ≠ .halted .exhausted) :
    M.observe data (bits ++ tail) c = M.observe data bits c := by
  unfold observe at *
  split
  · rfl
  · rfl
  · rename_i onFalse onTrue instruction
    rw [instruction] at h
    by_cases available : c.randomHead < bits.length
    · have extended : c.randomHead < (bits ++ tail).length := by
        simp only [List.length_append]
        omega
      rw [ite_eq_left available, ite_eq_left extended]
    · simp [available] at h
  · rfl

theorem next_append_of_observe_running (data : InputData I A)
    (bits tail : BitString) (c : Configuration M)
    (h : M.observe data bits c = .running c) :
    M.next data (bits ++ tail) c = M.next data bits c := by
  unfold observe at h
  unfold next
  split at h
  all_goals try contradiction
  all_goals try rfl
  have available : c.randomHead < bits.length := by
    by_cases available : c.randomHead < bits.length
    · exact available
    · simp [available] at h
  rw [List.getElem?_append_left available]

/-- Extending a random tape changes a run only if it previously exhausted that
tape. Acceptance and explicit rejection, as well as live configurations, persist. -/
theorem run_append_of_not_exhausted (data : InputData I A)
    (bits tail : BitString) (t : ℕ)
    (h : M.run data bits t ≠ .halted .exhausted) :
    M.run data (bits ++ tail) t = M.run data bits t := by
  induction t with
  | zero => exact M.observe_append_of_not_exhausted data bits tail M.initialConfiguration h
  | succ t ih =>
      cases previous : M.run data bits t with
      | halted result =>
          have good : M.run data bits t ≠ .halted .exhausted := by
            simpa only [run, previous] using h
          simp only [run, ih good, previous]
      | running c =>
          have good : M.run data bits t ≠ .halted .exhausted := by simp [previous]
          have observation := M.run_running_observe data bits t c previous
          have step := M.next_append_of_observe_running data bits tail c observation
          simp only [run, previous] at h
          simp only [run, ih good, previous, step]
          cases next : M.next data bits c with
          | halted result => rfl
          | running d =>
              apply M.observe_append_of_not_exhausted data bits tail d
              simpa [next] using h

theorem produces_append (data : InputData I A) (bits tail : BitString) (w : List O)
    (h : M.Produces data bits w) : M.Produces data (bits ++ tail) w := by
  obtain ⟨t, ht⟩ := h
  refine ⟨t, ?_⟩
  rw [M.run_append_of_not_exhausted data bits tail t (by simp [ht]), ht]

theorem produces_prefix {data : InputData I A} {bits longer : BitString} {w : List O}
    (hprefix : bits <+: longer) (h : M.Produces data bits w) : M.Produces data longer w := by
  obtain ⟨tail, rfl⟩ := hprefix
  exact M.produces_append data bits tail w h

theorem deterministic_observe (deterministic : M.Deterministic)
    (data : InputData I A) (bits other : BitString) (c : Configuration M) :
    M.observe data bits c = M.observe data other c := by
  have nonrandom := deterministic c.state data.input[c.inputHead]?
    data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some true else none) (c.work c.workHead)
  unfold observe
  split
  all_goals try rfl
  rename_i _ _ instruction
  simp [instruction] at nonrandom

theorem deterministic_next (deterministic : M.Deterministic)
    (data : InputData I A) (bits other : BitString) (c : Configuration M) :
    M.next data bits c = M.next data other c := by
  have nonrandom := deterministic c.state data.input[c.inputHead]?
    data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some true else none) (c.work c.workHead)
  unfold next
  split
  all_goals try rfl
  rename_i _ _ instruction
  simp [instruction] at nonrandom

/-- Deterministic machines cannot depend on random bits or on tape length. -/
theorem deterministic_run (deterministic : M.Deterministic)
    (data : InputData I A) (bits other : BitString) (t : ℕ) :
    M.run data bits t = M.run data other t := by
  induction t with
  | zero => exact M.deterministic_observe deterministic data bits other M.initialConfiguration
  | succ t ih =>
      simp only [run, ih]
      cases M.run data other t with
      | halted result => rfl
      | running c =>
          dsimp only
          rw [M.deterministic_next deterministic data bits other c]
          cases M.next data other c with
          | halted result => rfl
          | running d => exact M.deterministic_observe deterministic data bits other d

theorem deterministic_accepts (deterministic : M.Deterministic)
    (data : InputData I A) (bits other : BitString) :
    M.Accepts data bits ↔ M.Accepts data other := by
  unfold Accepts Produces
  simp_rw [M.deterministic_run deterministic data bits other]

end ComplexityOfGenerators.Machine
