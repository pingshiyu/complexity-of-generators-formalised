import ComplexityOfGenerators.Foundations.ExecutionPaths
import ComplexityOfGenerators.Foundations.SpaceConfigurations
import Mathlib.Logic.Relation

/-!
# Exact configuration-graph semantics for native space bounds

Edges forget only histories invisible to the finite transition table. Every
finite graph path is realizable by a finite random tape; conversely, every
accepting native run gives a path to an accepting vertex. With a space bound,
all vertices can be restricted to the existing finite configuration encoding.
This is the semantic input to space-bounded reachability, not a claim that graph
search has already been compiled to a native machine.
-/

namespace ComplexityOfGenerators.Machine

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

def DecisionView.Accepting (data : InputData I A) (c : M.DecisionView) : Prop :=
  M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work c.workHead) = .accept

/-- Each edge makes exactly one primitive transition. Only a `readRandom`
instruction uses the supplied Boolean choice. -/
def DecisionEdge (data : InputData I A) (c d : M.DecisionView) : Prop :=
  ∃ choice, c.advance M data choice = some d

theorem Steps.decisionPath {data : InputData I A} {bits : BitString}
    {start finish : Configuration M} {t : ℕ} (path : M.Steps data bits start t finish) :
    Relation.ReflTransGen (M.DecisionEdge data) (M.decisionView start) (M.decisionView finish) := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact ih.tail (M.next_decisionView _ _ _ _ step)

/-- Realize an edge by appending at most one random bit. Deterministic edges
consume no randomness, so arbitrarily long deterministic phases are allowed. -/
theorem decisionEdge_realize (data : InputData I A) (c : Configuration M)
    (d : M.DecisionView) (edge : M.DecisionEdge data (M.decisionView c) d)
    (bits : BitString) (consumed : c.randomHead = bits.length) :
    ∃ suffix : BitString, suffix.length ≤ 1 ∧ ∃ next : Configuration M,
      M.next data (bits ++ suffix) c = .running next ∧ M.decisionView next = d ∧
        next.randomHead = (bits ++ suffix).length := by
  obtain ⟨choice, edge⟩ := edge
  simp only [DecisionView.advance, decisionView] at edge
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) with
  | accept => simp only [action, reduceCtorEq] at edge
  | reject => simp only [action, reduceCtorEq] at edge
  | readRandom no yes =>
      let target : Configuration M :=
        {c with state := if choice then yes else no, randomHead := c.randomHead + 1}
      refine ⟨[choice], by simp, target, ?_, ?_, ?_⟩
      · simp [next, action, consumed, target]
      · exact Option.some.inj (by simpa [action, decisionView, target] using edge)
      · simp [consumed, target]
  | step state write work input auxiliary index emit =>
      refine ⟨[], by simp, M.stepConfiguration data c state write work input auxiliary index emit,
        ?_, ?_, ?_⟩
      · simpa using M.next_step data bits c state write work input auxiliary index emit action
      · cases write <;> simpa only [action, decisionView, stepConfiguration,
          Option.some.injEq] using edge
      · simpa [stepConfiguration] using consumed

/-- A graph path can be run on a finite random tape. Prefix padding is included
only for the arbitrary starting configuration's already-consumed random bits. -/
theorem decisionPath_realize (data : InputData I A) (start : Configuration M)
    {finish : M.DecisionView}
    (path : Relation.ReflTransGen (M.DecisionEdge data) (M.decisionView start) finish) :
    ∃ bits t next, M.Steps data bits start t next ∧ M.decisionView next = finish ∧
      next.randomHead = bits.length := by
  induction path with
  | refl => exact ⟨List.replicate start.randomHead false, 0, start, .refl, rfl, by simp⟩
  | @tail current finish path edge ih =>
      obtain ⟨bits, t, c, steps, same, consumed⟩ := ih
      rw [← same] at edge
      obtain ⟨suffix, _, d, step, view, random⟩ :=
        M.decisionEdge_realize data c finish edge bits consumed
      exact ⟨bits ++ suffix, t + 1, d, (steps.append M suffix).tail step, view, random⟩

theorem observe_accepted_iff (data : InputData I A) (bits : BitString) (c : Configuration M) :
    (∃ word, M.observe data bits c = .halted (.accepted word)) ↔
      (M.decisionView c).Accepting M data := by
  unfold observe DecisionView.Accepting decisionView
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
    (if c.indexHead < data.index then some () else none) (c.work c.workHead) <;> simp
  split_ifs <;> simp

/-- Exact acceptance semantics, without assuming halting, a time bound, or
bounded random-tape length. -/
theorem accepts_iff_decisionPath (data : InputData I A) :
    (∃ bits, M.Accepts data bits) ↔
      ∃ finish, Relation.ReflTransGen (M.DecisionEdge data)
        (M.decisionView M.initialConfiguration) finish ∧ finish.Accepting M data := by
  constructor
  · rintro ⟨bits, word, t, accepted⟩
    obtain ⟨s, _, finish, path, execution⟩ := M.runFrom_path data bits M.initialConfiguration t
    rw [runFrom_initial, accepted] at execution
    exact ⟨M.decisionView finish, path.decisionPath M,
      (M.observe_accepted_iff data bits finish).mp ⟨word, execution.symm⟩⟩
  · rintro ⟨finish, path, accepting⟩
    obtain ⟨bits, t, c, steps, same, _⟩ := M.decisionPath_realize data M.initialConfiguration path
    rw [← same] at accepting
    obtain ⟨word, observation⟩ := (M.observe_accepted_iff data bits c).mpr accepting
    refine ⟨bits, word, t, ?_⟩
    rw [← runFrom_initial, steps.runFrom M, observation]

theorem initial_decisionView_bounded (data : InputData I A) (s : ℕ) :
    (M.decisionView M.initialConfiguration).Bounded M data s := by
  constructor <;> simp [decisionView, initialConfiguration]

theorem SpaceBound.steps_decisionView_bounded {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) {bits : BitString} {t : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration t finish) :
    (M.decisionView finish).Bounded M data s := by
  cases path with
  | refl => exact M.initial_decisionView_bounded data s
  | @tail t current _ path step =>
      have execution := path.runFrom M
      rw [runFrom_initial, M.observe_of_next_running data bits current _ step] at execution
      exact space.next_decisionView_bounded M bits t current _ execution step

abbrev BoundedDecisionView (data : InputData I A) (s : ℕ) :=
  {c : M.DecisionView // c.Bounded M data s}

def boundedInitialView (data : InputData I A) (s : ℕ) : M.BoundedDecisionView data s :=
  ⟨M.decisionView M.initialConfiguration, M.initial_decisionView_bounded data s⟩

def BoundedDecisionEdge (data : InputData I A) (s : ℕ)
    (c d : M.BoundedDecisionView data s) : Prop := M.DecisionEdge data c.val d.val

theorem Steps.boundedDecisionPath {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) {bits : BitString} {t : ℕ} {finish : Configuration M}
    (path : M.Steps data bits M.initialConfiguration t finish) :
    Relation.ReflTransGen (M.BoundedDecisionEdge data s) (M.boundedInitialView data s)
      ⟨M.decisionView finish, space.steps_decisionView_bounded M path⟩ := by
  induction path with
  | refl => exact .refl
  | tail path step ih => exact ih.tail (M.next_decisionView _ _ _ _ step)

/-- A space-bounded native machine accepts iff an accepting vertex is reachable
in its finite configuration graph. Histories and random cursors are not encoded,
and every graph path still corresponds to a real finite-tape computation. -/
theorem SpaceBound.accepts_iff_boundedDecisionPath {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) :
    (∃ bits, M.Accepts data bits) ↔ ∃ finish : M.BoundedDecisionView data s,
      Relation.ReflTransGen (M.BoundedDecisionEdge data s) (M.boundedInitialView data s) finish ∧
        finish.val.Accepting M data := by
  constructor
  · rintro ⟨bits, word, t, accepted⟩
    obtain ⟨clock, _, finish, path, execution⟩ := M.runFrom_path data bits M.initialConfiguration t
    rw [runFrom_initial, accepted] at execution
    exact ⟨⟨M.decisionView finish, space.steps_decisionView_bounded M path⟩,
      path.boundedDecisionPath M space,
      (M.observe_accepted_iff data bits finish).mp ⟨word, execution.symm⟩⟩
  · rintro ⟨finish, path, accepting⟩
    apply (M.accepts_iff_decisionPath data).mpr
    exact ⟨finish.val, path.lift Subtype.val (fun _ _ edge => edge), accepting⟩

end ComplexityOfGenerators.Machine
