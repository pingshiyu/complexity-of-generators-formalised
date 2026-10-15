import ComplexityOfGenerators.Foundations.ExecutionPaths

/-! Machines whose work head always stays at the origin use exactly one
visited cell. Random-tape exhaustion does not change this bound. -/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

def StationaryWork : Prop :=
  ∀ q input auxiliary index cell,
    match M.transition q input auxiliary index cell with
    | .step _ _ work _ _ _ _ => work = .stay
    | _ => True

theorem Steps.stationary_work (stationary : M.StationaryWork)
    {data : InputData I A} {bits : BitString} {t : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration t finish) :
    finish.workHead = 0 ∧ finish.visited = {0} := by
  induction path with
  | refl => exact ⟨rfl, rfl⟩
  | @tail t c d path step ih =>
      have fixed := stationary c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
        (if c.indexHead < data.index then some () else none) (c.work c.workHead)
      cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
      | accept => simp [next, action] at step
      | reject => simp [next, action] at step
      | readRandom no yes =>
          cases lookup : bits[c.randomHead]? with
          | none => simp [next, action, lookup] at step
          | some bit =>
              simp only [next, action, lookup, RunState.running.injEq] at step
              cases step
              exact ih
      | step state write work input auxiliary index emit =>
          rw [action] at fixed
          subst work
          rw [M.next_step data bits c _ _ _ _ _ _ _ action] at step
          cases step
          simp [stepConfiguration, Move.onInt, ih.1, ih.2]

theorem StationaryWork.spaceBound (stationary : M.StationaryWork) (data : InputData I A) :
    M.SpaceBound data 1 := by
  refine ⟨by simp [initialConfiguration], ?_⟩
  intro bits t c running
  obtain ⟨u, _, finish, path, observation⟩ := M.runFrom_path data bits M.initialConfiguration t
  rw [runFrom_initial, running] at observation
  have same := M.observe_running_eq data bits finish c observation.symm
  subst c
  refine ⟨?_, ?_⟩
  · simp [(path.stationary_work M stationary).2]
  · intro d step
    simp [((path.tail step).stationary_work M stationary).2]

end ComplexityOfGenerators.Machine
