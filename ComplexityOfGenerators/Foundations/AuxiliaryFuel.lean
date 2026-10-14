import ComplexityOfGenerators.Foundations.ExecutionBounds

/-!
# A read-only certificate as a finite clock

If every nonterminal instruction consumes one auxiliary symbol, the auxiliary
tape bounds the run length. This is an operational bound on primitive native
steps, including malformed certificates and empty inputs.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

def AuxiliaryFuel : Prop :=
  ∀ q input auxiliary index work,
    match M.transition q input auxiliary index work with
    | .accept | .reject => True
    | .readRandom _ _ => False
    | .step _ _ _ _ move _ _ => auxiliary ≠ none ∧ move = .right

theorem AuxiliaryFuel.deterministic (fuel : M.AuxiliaryFuel) : M.Deterministic := by
  intro q input auxiliary index work
  have h := fuel q input auxiliary index work
  cases action : M.transition q input auxiliary index work <;> simp_all

theorem AuxiliaryFuel.next_progress (fuel : M.AuxiliaryFuel)
    (data : InputData I A) (bits : BitString) (c d : Configuration M)
    (step : M.next data bits c = .running d) :
    c.auxiliaryHead < data.auxiliary.length ∧ d.auxiliaryHead = c.auxiliaryHead + 1 := by
  have h := fuel c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work c.workHead)
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => simp [next, action] at step
  | reject => simp [next, action] at step
  | readRandom no yes => simp [action] at h
  | step state write work input auxiliary index emit =>
      simp only [action] at h
      obtain ⟨present, rfl⟩ := h
      have available : c.auxiliaryHead < data.auxiliary.length := by
        by_contra absent
        exact present (List.getElem?_eq_none_iff.mpr (by omega))
      rw [M.next_step data bits c state write work input .right index emit action] at step
      cases step
      exact ⟨available, by simp [stepConfiguration, Move.onInput,
        Nat.min_eq_left (show c.auxiliaryHead + 1 ≤ data.auxiliary.length by omega)]⟩

theorem AuxiliaryFuel.runFrom_halts (fuel : M.AuxiliaryFuel)
    (data : InputData I A) (bits : BitString) (remaining : ℕ) (c : Configuration M)
    (enough : data.auxiliary.length ≤ c.auxiliaryHead + remaining) :
    ∃ result, M.runFrom data bits c remaining = .halted result := by
  induction remaining generalizing c with
  | zero =>
      cases observation : M.observe data bits c with
      | halted result => exact ⟨result, observation⟩
      | running d =>
          have same := M.observe_running_eq data bits c d observation
          subst d
          obtain ⟨next, step⟩ := M.next_running_of_observe_running data bits c observation
          have := (fuel.next_progress M data bits c next step).1
          omega
  | succ remaining ih =>
      cases observation : M.observe data bits c with
      | halted result => exact ⟨result, M.runFrom_halted data bits c result observation _⟩
      | running d =>
          have same := M.observe_running_eq data bits c d observation
          subst d
          obtain ⟨next, step⟩ := M.next_running_of_observe_running data bits c observation
          have progress := (fuel.next_progress M data bits c next step).2
          obtain ⟨result, halted⟩ := ih next (by omega)
          exact ⟨result, (M.runFrom_shift data bits c next observation step remaining).trans halted⟩

theorem AuxiliaryFuel.timeBound (fuel : M.AuxiliaryFuel) (data : InputData I A) :
    M.TimeBound data data.auxiliary.length := by
  intro bits
  simpa only [HaltsWithin, runFrom_initial] using
    fuel.runFrom_halts M data bits data.auxiliary.length M.initialConfiguration (by
      simp [initialConfiguration])

end ComplexityOfGenerators.Machine
