import ComplexityOfGenerators.Simulation.CyclicGenerator.Decision

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

/-- Simulate a whole terminating decision using four bank instructions per
source transition. The random tape is untouched during the decision, and the
returned native source path retains its visited-cell accounting. -/
theorem decision_runFrom (deterministic : D.Deterministic)
    (word : List α) (seen : Bool) (random : ℕ) (bits : BitString)
    (c : Configuration D) (t : ℕ) (result : Outcome Unit)
    (source : D.runFrom (decisionData word) [] c t = .halted result)
    (geometry : D.TapeGeometry c) (headBound : c.inputHead ≤ word.length) :
    ∃ terminal u, u ≤ t ∧ D.Steps (decisionData word) [] c u terminal ∧
      (bank D).Steps (generatorData word.length) bits (decisionConfig D word seen random c) (4 * u)
        (decisionConfig D word seen random terminal) ∧
      D.observe (decisionData word) [] terminal = .halted result ∧
      D.TapeGeometry terminal ∧ terminal.inputHead ≤ word.length := by
  induction t generalizing c with
  | zero => exact ⟨c, 0, le_rfl, .refl, .refl _, source, geometry, headBound⟩
  | succ t ih =>
      cases observation : D.observe (decisionData word) [] c with
      | halted out =>
          have same := D.runFrom_halted (decisionData word) [] c out observation (t + 1)
          rw [source] at same
          cases same
          exact ⟨c, 0, Nat.zero_le _, .refl, .refl _, observation, geometry, headBound⟩
      | running current =>
          have same := D.observe_running_eq _ [] c current observation
          subst current
          obtain ⟨d, next⟩ := D.next_running_of_observe _ [] c observation
          rw [D.runFrom_shift _ [] c d observation next t] at source
          cases action : D.transition c.state word[c.inputHead]? none none (c.work c.workHead) with
          | accept => simp [Machine.observe, decisionData, action] at observation
          | reject => simp [Machine.observe, decisionData, action] at observation
          | readRandom no yes =>
              have impossible := deterministic c.state word[c.inputHead]? none none (c.work c.workHead)
              rw [action] at impossible
              exact False.elim impossible
          | step state write work input auxiliary index emit =>
              have actual : D.transition c.state (decisionData word).input[c.inputHead]?
                  (decisionData word).auxiliary[c.auxiliaryHead]?
                  (if c.indexHead < (decisionData word).index then some () else none) (c.work c.workHead) =
                  .step state write work input auxiliary index emit := by simpa [decisionData] using action
              rw [D.next_step _ [] c _ _ _ _ _ _ _ actual] at next
              cases next
              obtain ⟨terminal, u, length, path, simulation, halted, finalGeometry, finalBound⟩ :=
                ih _ source (D.stepConfiguration_geometry _ _ geometry _ _ _ _ _ _ _)
                  (input.onInput_le _ _ headBound)
              have one := decision_step D word seen random bits c headBound geometry.head
                state write work input auxiliary index emit action
              refine ⟨terminal, u + 1, by omega, ?_, ?_, halted, finalGeometry, finalBound⟩
              · simpa [Nat.add_comm] using
                  (Machine.Steps.tail .refl (D.next_step _ [] c _ _ _ _ _ _ _ actual)).trans D path
              · simpa [Nat.mul_add, Nat.add_comm] using one.trans (bank D) simulation

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
