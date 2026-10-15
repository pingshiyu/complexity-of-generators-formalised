import ComplexityOfGenerators.Foundations.ExecutionPaths

/-!
# Space bounds from complete native execution paths

Visited cells are monotone along primitive paths. Consequently a bound on the
last configuration of a terminating path bounds every prefix, including the
successor immediately before terminal observation. The running time need not
be bounded by the space budget.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

theorem next_visited_subset (data : InputData I A) (bits : BitString)
    {a b : Configuration M} (step : M.next data bits a = .running b) :
    a.visited ⊆ b.visited := by
  unfold next at step
  split at step
  · cases step
  · cases step
  · split at step
    · cases step
    · cases step; exact Finset.Subset.refl _
  · cases step; exact Finset.subset_insert _ _

theorem Steps.visited_subset {data : InputData I A} {bits : BitString}
    {a b : Configuration M} {t : ℕ} (path : M.Steps data bits a t b) :
    a.visited ⊆ b.visited := by
  induction path with
  | refl => exact Finset.Subset.refl _
  | tail path step ih => exact ih.trans (M.next_visited_subset _ _ step)

theorem Steps.trans {data : InputData I A} {bits : BitString}
    {a b c : Configuration M} {s t : ℕ} (left : M.Steps data bits a s b)
    (right : M.Steps data bits b t c) : M.Steps data bits a (s + t) c := by
  induction right with
  | refl => exact left
  | tail path step ih => exact ih.tail step

theorem Steps.unique {data : InputData I A} {bits : BitString}
    {a b c : Configuration M} {t : ℕ} (left : M.Steps data bits a t b)
    (right : M.Steps data bits a t c) : b = c := by
  induction left generalizing c with
  | refl => cases right; rfl
  | tail path step ih =>
      cases right with
      | tail path' step' =>
          have same := ih path'
          subst same
          exact RunState.running.inj (step.symm.trans step')

theorem Steps.first {data : InputData I A} {bits : BitString} {n : ℕ}
    {a b : Configuration M} (path : M.Steps data bits a (n + 1) b) :
    ∃ c, M.next data bits a = .running c ∧ M.Steps data bits c n b := by
  induction n generalizing a b with
  | zero => cases path with | tail rest step => cases rest; exact ⟨_, step, .refl⟩
  | succ n ih =>
      cases path with
      | tail rest step =>
          obtain ⟨c, first, rest⟩ := ih rest
          exact ⟨c, first, rest.tail step⟩

theorem Steps.split {data : InputData I A} {bits : BitString}
    {a b : Configuration M} {t : ℕ} (path : M.Steps data bits a t b)
    (n : ℕ) (bound : n ≤ t) :
    ∃ c, M.Steps data bits a n c ∧ M.Steps data bits c (t - n) b := by
  induction path with
  | refl =>
      have : n = 0 := by omega
      subst n
      exact ⟨_, .refl, .refl⟩
  | @tail t current next path step ih =>
      by_cases last : n = t + 1
      · subst n; exact ⟨_, path.tail step, by simp; exact .refl⟩
      · obtain ⟨c, left, right⟩ := ih (by omega)
        refine ⟨c, left, ?_⟩
        have length : t + 1 - n = (t - n) + 1 := by omega
        rw [length]
        exact right.tail step

theorem Steps.prefix_visited {data : InputData I A} {bits : BitString}
    {a b c : Configuration M} {s t : ℕ} (left : M.Steps data bits a s b)
    (right : M.Steps data bits a t c) (bound : s ≤ t) : b.visited ⊆ c.visited := by
  obtain ⟨middle, initialPath, rest⟩ := right.split M s bound
  have same := left.unique M initialPath
  subst middle
  exact rest.visited_subset M

/-- No primitive path on the same tape can extend past a terminal endpoint. -/
theorem Steps.le_terminal {data : InputData I A} {bits : BitString}
    {a b c : Configuration M} {s t : ℕ} (path : M.Steps data bits a s b)
    (complete : M.Steps data bits a t c) {result : Outcome O}
    (terminal : M.observe data bits c = .halted result) : s ≤ t := by
  by_contra longer
  obtain ⟨middle, initialPath, rest⟩ := path.split M t (by omega)
  have same := complete.unique M initialPath
  subst middle
  have length : s - t = (s - t - 1) + 1 := by omega
  rw [length] at rest
  obtain ⟨next, step, _⟩ := rest.first M
  have live := M.observe_of_next_running data bits c next step
  rw [terminal] at live
  cases live

/-- Bounding the visited set of every terminal path suffices for the native
space convention, without any uniform bound on path length. -/
theorem spaceBound_of_terminal_paths (data : InputData I A) (s : ℕ)
    (complete : ∀ bits, ∃ t finish result,
      M.Steps data bits M.initialConfiguration t finish ∧
      M.observe data bits finish = .halted result ∧ finish.visited.card ≤ s) :
    M.SpaceBound data s := by
  have bound (bits : BitString) (t : ℕ) (c : Configuration M)
      (path : M.Steps data bits M.initialConfiguration t c) : c.visited.card ≤ s := by
    obtain ⟨u, finish, result, finalPath, terminal, size⟩ := complete bits
    exact (Finset.card_le_card (path.prefix_visited M finalPath
      (path.le_terminal M finalPath terminal))).trans size
  refine ⟨bound [] 0 _ .refl, ?_⟩
  intro bits t c running
  obtain ⟨u, _, finish, path, observation⟩ := M.runFrom_path data bits M.initialConfiguration t
  rw [runFrom_initial, running] at observation
  have same := M.observe_running_eq data bits finish c observation.symm
  subst finish
  exact ⟨bound bits u c path, fun next step => bound bits (u + 1) next (path.tail step)⟩

/-- A fixed interval of work cells. Repeated passes through this interval do
not increase its size. -/
def InRegion (r : ℕ) (c : Configuration M) : Prop :=
  ∀ i ∈ c.visited, -(r : ℤ) ≤ i ∧ i ≤ (r : ℤ)

theorem coordinate_bounds {r : ℕ} {i : ℤ} (bound : i.natAbs ≤ r) :
    -(r : ℤ) ≤ i ∧ i ≤ (r : ℤ) := by
  cases i <;> simp_all
  omega

theorem InRegion.card_le {r : ℕ} {c : Configuration M} (h : M.InRegion r c) :
    c.visited.card ≤ 2 * r + 1 := by
  have subset : c.visited ⊆ Finset.Icc (-(r : ℤ)) (r : ℤ) := by
    intro i hi; exact Finset.mem_Icc.mpr (h i hi)
  have bound := Finset.card_le_card subset
  have count : (Finset.Icc (-(r : ℤ)) (r : ℤ)).card = 2 * r + 1 := by
    rw [Int.card_Icc]
    omega
  rwa [count] at bound

theorem initial_inRegion (r : ℕ) : M.InRegion r M.initialConfiguration := by
  intro i hi
  have : i = 0 := by simpa [initialConfiguration] using hi
  subst i
  constructor <;> omega

theorem InRegion.step {r : ℕ} {c : Configuration M} (h : M.InRegion r c)
    (data : InputData I A) (state : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O)
    (head : -(r : ℤ) ≤ work.onInt c.workHead ∧ work.onInt c.workHead ≤ r) :
    M.InRegion r (M.stepConfiguration data c state write work input auxiliary index emit) := by
  intro i hi
  rcases Finset.mem_insert.mp hi with rfl | hi
  · exact head
  · exact h i hi

end ComplexityOfGenerators.Machine
