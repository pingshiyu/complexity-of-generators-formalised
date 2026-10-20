import ComplexityOfGenerators.Simulation.NativeNTM.Step
import ComplexityOfGenerators.Simulation.NativeNTM.Prelude

/-! Exact acceptance and space preservation after initialization. Infinite
choice paths are allowed; every finite native graph path uses a finite tape. -/

namespace ComplexityOfGenerators.Simulation.NativeNTM
open Complexity
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine α Bool Unit)

def NativeReach (word : List α) (v : M.DecisionView) : Prop :=
  Relation.ReflTransGen (M.DecisionEdge (sourceData word)) (M.decisionView M.initialConfiguration) v

theorem native_bound (word : List α) (s : ℕ) (space : M.SpaceBound (sourceData word) s)
    (v : M.DecisionView) (path : NativeReach M word v) : v.Bounded M (sourceData word) s := by
  obtain ⟨bits, t, c, steps, same, _⟩ := M.decisionPath_realize (sourceData word) M.initialConfiguration path
  rw [← same]
  exact space.steps_decisionView_bounded M steps

def Represents (full : BitString) (word : List α)
    (c : Cfg (Fintype.card (Tracks M)) (tm M).Q) : Prop :=
  ∃ v, NativeReach M word v ∧ ∃ negative p, v.workHead = coordinate negative p ∧
    (c = simulated M full word v negative p ∨
      ∃ verdict, c = finished M full word v p verdict ∧
        sourceAction M word v = if verdict then .accept else .reject)

theorem advance_random (word : List α) (v : M.DecisionView) (bit : Bool) (no yes : Fin M.states)
    (action : sourceAction M word v = .readRandom no yes) :
    v.advance M (sourceData word) bit = some {v with state := if bit then yes else no} := by
  dsimp [sourceAction] at action
  simp [Machine.DecisionView.advance, sourceData, action]

theorem advance_step (word : List α) (v : M.DecisionView) (bit : Bool) (q : Fin M.states)
    (write : Option (Fin M.symbols)) (work input auxiliary index : Move) (emit : Option Unit)
    (action : sourceAction M word v = .step q write work input auxiliary index emit) :
    v.advance M (sourceData word) bit = some (nextView M word v q write work input auxiliary index) := by
  dsimp [sourceAction] at action
  simp [Machine.DecisionView.advance, sourceData, action, nextView]
  cases write <;> rfl

theorem reachable_represents (full : BitString) (word : List α) (s : ℕ)
    (space : M.SpaceBound (sourceData word) s)
    (c : Cfg (Fintype.card (Tracks M)) (tm M).Q)
    (path : (tm M).ReachesCfg (simulated M full word (M.decisionView M.initialConfiguration) false 0) c) :
    Represents M full word c := by
  induction path with
  | refl => exact ⟨_, .refl, false, 0, rfl, Or.inl rfl⟩
  | @tail current finish path step ih =>
    obtain ⟨v, native, negative, p, head, ready | ⟨verdict, terminal, _⟩⟩ := ih
    · subst current
      obtain ⟨_, bit, rfl⟩ := step
      have bound := native_bound M word s space v native
      cases action : sourceAction M word v with
      | accept =>
        exact ⟨v, native, negative, p, head, Or.inr ⟨true,
          step_terminal M bit full word v negative p head true action, action⟩⟩
      | reject =>
        exact ⟨v, native, negative, p, head, Or.inr ⟨false,
          step_terminal M bit full word v negative p head false action, action⟩⟩
      | readRandom no yes =>
        exact ⟨_, native.tail ⟨bit, advance_random M word v bit no yes action⟩,
          negative, p, head, Or.inl (step_random M bit full word v negative p head no yes action)⟩
      | step q write work input auxiliary index emit =>
        refine ⟨_, native.tail ⟨bit, advance_step M word v bit q write work input auxiliary index emit action⟩,
          foldedSign negative (decide (p = 0)) work, foldedHead negative p work, ?_, Or.inl ?_⟩
        · simp only [nextView, coordinate_foldedHead, head]
        · exact step_native M bit full word v negative p head bound.inputHead bound.indexHead
            q write work input auxiliary index emit action
    · subst current
      exact (step.1 (finished_halted M full word v p verdict)).elim

theorem native_path (full : BitString) (word : List α) (s : ℕ)
    (space : M.SpaceBound (sourceData word) s) (v : M.DecisionView) (path : NativeReach M word v) :
    ∃ negative p, v.workHead = coordinate negative p ∧
      (tm M).ReachesCfg (simulated M full word (M.decisionView M.initialConfiguration) false 0)
        (simulated M full word v negative p) := by
  induction path with
  | refl => exact ⟨false, 0, rfl, .refl⟩
  | @tail v d path edge ih =>
    obtain ⟨negative, p, head, previous⟩ := ih
    obtain ⟨bit, edge⟩ := edge
    have bound := native_bound M word s space v path
    have live : (simulated M full word v negative p).state ≠ (tm M).qhalt := by
      intro h; cases h
    cases action : sourceAction M word v with
    | accept =>
      dsimp [sourceAction] at action
      simp [Machine.DecisionView.advance, sourceData, action] at edge
    | reject =>
      dsimp [sourceAction] at action
      simp [Machine.DecisionView.advance, sourceData, action] at edge
    | readRandom no yes =>
      rw [advance_random M word v bit no yes action] at edge
      cases edge
      exact ⟨negative, p, head, previous.tail ⟨live, bit,
        (step_random M bit full word v negative p head no yes action).symm⟩⟩
    | step q write work input auxiliary index emit =>
      rw [advance_step M word v bit q write work input auxiliary index emit action] at edge
      cases edge
      refine ⟨foldedSign negative (decide (p = 0)) work, foldedHead negative p work,
        ?_, previous.tail ⟨live, bit, ?_⟩⟩
      · simp only [nextView, coordinate_foldedHead, head]
      · exact (step_native M bit full word v negative p head bound.inputHead bound.indexHead
          q write work input auxiliary index emit action).symm

theorem simulated_accepts_iff (full : BitString) (word : List α) (s : ℕ)
    (space : M.SpaceBound (sourceData word) s) :
    (∃ c, (tm M).ReachesCfg (simulated M full word (M.decisionView M.initialConfiguration) false 0) c ∧
      (tm M).halted c ∧ c.output.cells 1 = .one) ↔ ∃ bits, M.Accepts (sourceData word) bits := by
  rw [M.accepts_iff_decisionPath]
  constructor
  · rintro ⟨c, path, halt, output⟩
    obtain ⟨v, native, negative, p, head, rfl | ⟨verdict, rfl, action⟩⟩ :=
      reachable_represents M full word s space c path
    · cases halt
    · have yes := (finished_output M full word v p verdict).mp output
      subst verdict
      refine ⟨v, native, ?_⟩
      simpa [Machine.DecisionView.Accepting, sourceData, sourceAction] using action
  · rintro ⟨v, native, accept⟩
    obtain ⟨negative, p, head, path⟩ := native_path M full word s space v native
    have action : sourceAction M word v = .accept := by
      simpa [Machine.DecisionView.Accepting, sourceData, sourceAction] using accept
    refine ⟨_, path.tail ⟨?_, false, (step_terminal M false full word v negative p head true action).symm⟩,
      finished_halted M full word v p true, (finished_output M full word v p true).mpr rfl⟩
    intro h; cases h

theorem represented_space (full : BitString) (word : List α) (s : ℕ)
    (space : M.SpaceBound (sourceData word) s) (length : word.length ≤ full.length)
    (c : Cfg (Fintype.card (Tracks M)) (tm M).Q) (rep : Represents M full word c) :
    c.WithinDecisionSpace full.length (full.length + s + 1) := by
  obtain ⟨v, native, negative, p, head, rfl | ⟨verdict, rfl, _⟩⟩ := rep
  all_goals
    have bound := native_bound M word s space v native
    have hp : p ≤ s := by simpa only [head, coordinate_natAbs] using bound.workHead
    refine ⟨⟨fun i => ?_, ?_⟩, ?_⟩
    · apply tracks_bound
      · have := bound.inputHead; change v.inputHead ≤ word.length at this; omega
      · have := bound.indexHead; change v.indexHead ≤ word.length at this; omega
      · omega
    · change full.length + 1 ≤ _; omega
    · change 1 ≤ _; omega

end
end ComplexityOfGenerators.Simulation.NativeNTM
