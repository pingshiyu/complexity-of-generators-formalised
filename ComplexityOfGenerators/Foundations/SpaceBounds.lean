import ComplexityOfGenerators.Foundations.ExecutionBounds
import Mathlib.Data.Int.Interval

/-!
# Geometry of the native work tape

Space counts visited cells, rather than the current head coordinate. A reachable
tape nevertheless has no gaps in its visited region: it is an integer interval
containing the origin and the head, and all cells outside it are blank. These
invariants turn a space bound into a finite window for configuration encodings.
They hold also immediately after a transition into a terminal configuration.
-/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

structure TapeGeometry (c : Configuration M) : Prop where
  interval : ∃ lo hi : ℤ, lo ≤ 0 ∧ 0 ≤ hi ∧ c.visited = Finset.Icc lo hi
  head : c.workHead ∈ c.visited
  blank : ∀ i, i ∉ c.visited → c.work i = none

theorem initialConfiguration_geometry : M.TapeGeometry M.initialConfiguration := by
  refine ⟨⟨0, 0, le_rfl, le_rfl, by simp [initialConfiguration]⟩, ?_, ?_⟩
  · simp [initialConfiguration]
  · intro i _
    rfl

private theorem insert_interval (lo hi i : ℤ) (_ordered : lo ≤ hi)
    (lower : lo - 1 ≤ i) (upper : i ≤ hi + 1) :
    insert i (Finset.Icc lo hi) = Finset.Icc (min lo i) (max hi i) := by
  ext j
  simp only [Finset.mem_insert, Finset.mem_Icc, min_le_iff, le_max_iff]
  omega

theorem stepConfiguration_geometry (data : InputData I A) (c : Configuration M)
    (h : M.TapeGeometry c) (state : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O) :
    M.TapeGeometry (M.stepConfiguration data c state write work input auxiliary index emit) := by
  obtain ⟨lo, hi, lower, upper, region⟩ := h.interval
  have headBounds : lo ≤ c.workHead ∧ c.workHead ≤ hi := by
    simpa only [region, Finset.mem_Icc] using h.head
  have movedLower : lo - 1 ≤ work.onInt c.workHead := by
    cases work <;> simp only [Move.onInt] <;> omega
  have movedUpper : work.onInt c.workHead ≤ hi + 1 := by
    cases work <;> simp only [Move.onInt] <;> omega
  refine ⟨⟨min lo (work.onInt c.workHead), max hi (work.onInt c.workHead),
    (min_le_left _ _).trans lower, upper.trans (le_max_left _ _), ?_⟩, ?_, ?_⟩
  · change insert _ c.visited = _
    rw [region]
    exact insert_interval lo hi _ (by omega) movedLower movedUpper
  · exact Finset.mem_insert_self _ _
  · intro i outside
    have oldOutside : i ∉ c.visited := fun inside => outside (Finset.mem_insert_of_mem inside)
    have different : i ≠ c.workHead := fun same => oldOutside (same ▸ h.head)
    cases write with
    | none => exact h.blank i oldOutside
    | some symbol =>
        change Function.update c.work c.workHead (some symbol) i = none
        rw [Function.update_of_ne different]
        exact h.blank i oldOutside

theorem next_geometry (data : InputData I A) (bits : BitString) (c d : Configuration M)
    (h : M.TapeGeometry c) (step : M.next data bits c = .running d) : M.TapeGeometry d := by
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => simp [next, action] at step
  | reject => simp [next, action] at step
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [next, action, lookup] at step
      | some bit =>
          simp only [next, action, lookup, RunState.running.injEq] at step
          subst d
          exact ⟨h.interval, h.head, h.blank⟩
  | step state write work input auxiliary index emit =>
      rw [M.next_step data bits c state write work input auxiliary index emit action] at step
      cases step
      exact M.stepConfiguration_geometry data c h state write work input auxiliary index emit

theorem run_geometry (data : InputData I A) (bits : BitString) (t : ℕ)
    (c : Configuration M) (execution : M.run data bits t = .running c) : M.TapeGeometry c := by
  induction t generalizing c with
  | zero =>
      have same := M.observe_running_eq data bits M.initialConfiguration c execution
      rw [same]
      exact M.initialConfiguration_geometry
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
              rw [same]
              exact M.next_geometry data bits current next (ih current previous) step

/-- Each visited coordinate lies in the finite window determined by the number
of visited cells, even on computations whose running time is unbounded. -/
theorem TapeGeometry.coordinate_bound {c : Configuration M} (h : M.TapeGeometry c)
    (i : ℤ) (inside : i ∈ c.visited) : i.natAbs + 1 ≤ c.visited.card := by
  obtain ⟨lo, hi, lower, upper, region⟩ := h.interval
  have coordinate : lo ≤ i ∧ i ≤ hi := by simpa only [region, Finset.mem_Icc] using inside
  have count : (c.visited.card : ℤ) = hi + 1 - lo := by
    rw [region]
    exact Int.card_Icc_of_le (a := lo) (b := hi) (by omega)
  cases i <;> simp_all <;> omega

theorem TapeGeometry.workHead_bound {c : Configuration M} (h : M.TapeGeometry c) :
    c.workHead.natAbs + 1 ≤ c.visited.card :=
  h.coordinate_bound M c.workHead h.head

theorem TapeGeometry.blank_outside_window {c : Configuration M} (h : M.TapeGeometry c)
    {s : ℕ} (bound : c.visited.card ≤ s) (i : ℤ) (outside : s ≤ i.natAbs) :
    c.work i = none := by
  apply h.blank
  intro inside
  have := h.coordinate_bound M i inside
  omega

theorem SpaceBound.mono {data : InputData I A} {s t : ℕ}
    (h : M.SpaceBound data s) (le : s ≤ t) : M.SpaceBound data t := by
  refine ⟨h.1.trans le, ?_⟩
  intro bits clock c running
  obtain ⟨current, next⟩ := h.2 bits clock c running
  exact ⟨current.trans le, fun d step => (next d step).trans le⟩

/-- A time-bounded native computation visits at most one new cell per step,
in addition to the initially visited origin. The terminal successor counts. -/
theorem TimeBound.spaceBound {data : InputData I A} {t : ℕ}
    (h : M.TimeBound data t) : M.SpaceBound data (t + 1) := by
  refine ⟨by simp [initialConfiguration], ?_⟩
  intro bits clock c running
  have before : clock < t := by
    by_contra later
    obtain ⟨result, halted⟩ := h bits
    have persist := M.run_halted_add data bits t result halted (clock - t)
    have clockEq : t + (clock - t) = clock := by omega
    rw [clockEq, running] at persist
    cases persist
  have bound := M.run_configurationBound data bits clock c running
  refine ⟨bound.visited.trans (by omega), ?_⟩
  intro d step
  have nextBound := M.next_executionBound data bits clock c bound
  rw [step] at nextBound
  exact nextBound.visited.trans (by omega)

end ComplexityOfGenerators.Machine
