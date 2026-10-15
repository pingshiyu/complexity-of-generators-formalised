import ComplexityOfGenerators.Foundations.SpaceBounds

/-!
# Native execution paths, including terminal successor configurations

`Steps` records primitive transitions before terminal observation. Unlike a
running configuration returned by `run`, its endpoint may already accept,
reject, or request a random bit beyond the supplied tape. This distinction is
needed when connecting finite configuration graphs to actual executions and
when bounding the space used by the last transition.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

/-- A path of actual primitive transitions, with terminal observation deferred
at its endpoint. Every edge still uses the original finite random tape. -/
inductive Steps (data : InputData I A) (bits : BitString) (start : Configuration M) :
    ℕ → Configuration M → Prop
  | refl : Steps data bits start 0 start
  | tail {t current next} : Steps data bits start t current →
      M.next data bits current = .running next → Steps data bits start (t + 1) next

theorem observe_of_next_running (data : InputData I A) (bits : BitString)
    (c d : Configuration M) (step : M.next data bits c = .running d) :
    M.observe data bits c = .running c := by
  unfold next at step
  unfold observe
  split at step <;> rename_i action
  · cases step
  · cases step
  · split at step
    · cases step
    · rename_i bit lookup
      have bound := List.getElem?_eq_some_iff.mp lookup
      simp only [ite_eq_left bound.1]
  · rfl

theorem next_running_of_observe (data : InputData I A) (bits : BitString)
    (c : Configuration M) (live : M.observe data bits c = .running c) :
    ∃ d, M.next data bits c = .running d := by
  unfold observe at live
  unfold next
  split at live <;> rename_i action
  · cases live
  · cases live
  · split_ifs at live with bound
    · simp only [List.getElem?_eq_getElem bound]
      exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

theorem Steps.runFrom {data : InputData I A} {bits : BitString}
    {start finish : Configuration M} {t : ℕ} (path : M.Steps data bits start t finish) :
    M.runFrom data bits start t = M.observe data bits finish := by
  induction path with
  | refl => rfl
  | @tail t current next path step ih =>
      rw [M.runFrom_add data bits start current t ih 1]
      exact M.runFrom_shift data bits current next
        (M.observe_of_next_running data bits current next step) step 0

theorem Steps.append {data : InputData I A} {bits : BitString}
    {start finish : Configuration M} {t : ℕ} (path : M.Steps data bits start t finish)
    (suffix : BitString) : M.Steps data (bits ++ suffix) start t finish := by
  induction path with
  | refl => exact .refl
  | @tail t current next path step ih =>
      apply ih.tail
      rw [M.next_append_of_observe_running data bits suffix current
        (M.observe_of_next_running data bits current next step)]
      exact step

/-- The evaluator is an actual transition path followed by observation. A
halted result is padded in time, without inventing additional path edges. -/
theorem runFrom_path (data : InputData I A) (bits : BitString)
    (start : Configuration M) (t : ℕ) :
    ∃ s ≤ t, ∃ finish, M.Steps data bits start s finish ∧
      M.runFrom data bits start t = M.observe data bits finish := by
  induction t with
  | zero => exact ⟨0, le_rfl, start, .refl, rfl⟩
  | succ t ih =>
      obtain ⟨s, bound, finish, path, execution⟩ := ih
      cases observation : M.observe data bits finish with
      | halted result =>
          refine ⟨s, by omega, finish, path, ?_⟩
          simp only [runFrom, execution, observation]
      | running current =>
          have same := M.observe_running_eq data bits finish current observation
          subst current
          obtain ⟨next, step⟩ := M.next_running_of_observe data bits finish observation
          refine ⟨s + 1, by omega, next, path.tail step, ?_⟩
          simp only [runFrom, execution, observation, step]

/-- A space bound covers endpoints even when observation halts immediately
there. This is the terminal-successor clause of the native space convention. -/
theorem SpaceBound.steps_visited {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) {bits : BitString} {t : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration t finish) : finish.visited.card ≤ s := by
  cases path with
  | refl => exact space.1
  | @tail t current next path step =>
      have execution := path.runFrom M
      rw [runFrom_initial, M.observe_of_next_running data bits current _ step] at execution
      exact (space.2 bits t current execution).2 _ step

end ComplexityOfGenerators.Machine
