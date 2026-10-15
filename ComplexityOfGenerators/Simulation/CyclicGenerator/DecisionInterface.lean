import ComplexityOfGenerators.Simulation.CyclicGenerator.DecisionSpace
import ComplexityOfGenerators.Simulation.CyclicGenerator.Entry

/-! A complete candidate test, from a clean word configuration to a terminal
source decision. Its region bound is polynomial even when the test is slow. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

def radius (n s : ℕ) : ℕ := 5 * (n + s + 1)

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem candidate_bounded (word : List α) (seen : Bool) (random position : ℕ)
    (bound : position ≤ word.length) :
    (bank D).Bounded (generatorData word.length) word.length (candidateConfig D word seen random position) := by
  constructor
  · simp [candidateConfig, generatorData]
  · simp [candidateConfig, generatorData]
  · simp [candidateConfig, generatorData]
  · intro j
    fin_cases j <;> simp [candidateConfig] <;> omega

theorem candidate_entry_inRegion (word : List α) (seen : Bool) (random position s : ℕ)
    (bits : BitString) (bound : position ≤ word.length) :
    (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
      (candidateConfig D word seen random position) (position + 3)
      (decisionConfig D word seen random D.initialConfiguration) :=
  ((candidate_entry D word seen random position bits).inRegion (bank D) word.length
    (candidate_bounded D word seen random position bound)).mono (bank D) (by unfold radius; omega)

/-- A terminating native decision reaches either its accepting or rejecting
instruction. The configuration includes the visited cells of its last step. -/
theorem terminal_decision (deterministic : D.Deterministic) (word : List α)
    (halts : D.Halts (decisionData word) []) :
    ∃ t terminal, D.Steps (decisionData word) [] D.initialConfiguration t terminal ∧
      (D.transition terminal.state word[terminal.inputHead]? none none
        (terminal.work terminal.workHead) = .accept ∨
       D.transition terminal.state word[terminal.inputHead]? none none
        (terminal.work terminal.workHead) = .reject) ∧
      (D.transition terminal.state word[terminal.inputHead]? none none
        (terminal.work terminal.workHead) = .accept ↔ D.Accepts (decisionData word) []) := by
  obtain ⟨clock, result, halted⟩ := halts
  obtain ⟨t, _, terminal, path, observe⟩ := D.runFrom_path (decisionData word) [] D.initialConfiguration clock
  rw [Machine.runFrom_initial, halted] at observe
  have terminalRun := path.runFrom D
  rw [Machine.runFrom_initial, ← observe] at terminalRun
  refine ⟨t, terminal, path, ?_, ?_⟩
  · cases action : D.transition terminal.state word[terminal.inputHead]? none none
        (terminal.work terminal.workHead) with
    | accept => exact Or.inl rfl
    | reject => exact Or.inr rfl
    | readRandom no yes =>
        have impossible := deterministic terminal.state word[terminal.inputHead]? none none
          (terminal.work terminal.workHead)
        rw [action] at impossible
        exact False.elim impossible
    | step => simp [Machine.observe, decisionData, action] at observe
  · constructor
    · intro accepts
      have resultEq : result = .accepted terminal.output := by
        simpa [Machine.observe, decisionData, accepts] using observe
      exact ⟨terminal.output, t, resultEq ▸ terminalRun⟩
    · rintro ⟨output, ticks, accepted⟩
      have same := D.halted_outcome_unique _ [] t ticks result (.accepted output) terminalRun accepted
      rw [same] at observe
      cases action : D.transition terminal.state word[terminal.inputHead]? none none
          (terminal.work terminal.workHead) <;> simp [Machine.observe, decisionData, action] at observe ⊢

theorem candidate_decision (deterministic : D.Deterministic)
    (word : List α) (seen : Bool) (random position s : ℕ) (bits : BitString)
    (positionBound : position ≤ word.length) (halts : D.Halts (decisionData word) [])
    (space : D.SpaceBound (decisionData word) s) :
    ∃ ticks terminal,
      (bank D).RegionSteps (generatorData word.length) bits (radius word.length s)
        (candidateConfig D word seen random position) ticks (decisionConfig D word seen random terminal) ∧
      D.TapeGeometry terminal ∧ terminal.visited.card ≤ s ∧ terminal.inputHead ≤ word.length ∧
      (D.transition terminal.state word[terminal.inputHead]? none none
        (terminal.work terminal.workHead) = .accept ∨
       D.transition terminal.state word[terminal.inputHead]? none none
        (terminal.work terminal.workHead) = .reject) ∧
      (D.transition terminal.state word[terminal.inputHead]? none none
        (terminal.work terminal.workHead) = .accept ↔ D.Accepts (decisionData word) []) := by
  obtain ⟨t, terminal, path, action, accepts⟩ := terminal_decision D deterministic word halts
  obtain ⟨simulated, geometry⟩ := decision_steps_inRegion D deterministic word seen random s bits space path
  have entry := candidate_entry_inRegion D word seen random position s bits positionBound
  have region := simulated.mono (bank D) (show word.length + s + 4 ≤ radius word.length s by
    unfold radius; omega)
  exact ⟨_, terminal, entry.trans (bank D) region, geometry, space.steps_visited D path,
    (space.steps_decisionView_bounded D path).inputHead, action, accepts⟩

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
