import ComplexityOfGenerators.Simulation.CyclicGenerator.DecisionRun
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import ComplexityOfGenerators.Foundations.SpaceReachability

/-! Space accounting for the cyclic generator's decision subroutine. Each
four-instruction simulation block stays within four cells of a source head.
Composing the blocks does not increase that radius. -/

namespace ComplexityOfGenerators.Simulation.CyclicGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem decisionConfig_bounded (word : List α) (seen : Bool) (random s : ℕ)
    (c : Configuration D) (input : c.inputHead ≤ word.length) (work : c.workHead.natAbs ≤ s) :
    (bank D).Bounded (generatorData word.length) (word.length + s)
      (decisionConfig D word seen random c) := by
  constructor
  · simp [decisionConfig, generatorData]
  · simp [decisionConfig, generatorData]
  · simp [decisionConfig, generatorData]
  · intro j
    fin_cases j <;> simp [decisionConfig] <;> omega

/-- All source steps, including the last transition into a terminal state,
are simulated inside one fixed region. -/
theorem decision_steps_inRegion (deterministic : D.Deterministic)
    (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (space : D.SpaceBound (decisionData word) s) {t : ℕ} {c : Configuration D}
    (path : D.Steps (decisionData word) [] D.initialConfiguration t c) :
    (bank D).RegionSteps (generatorData word.length) bits (word.length + s + 4)
      (decisionConfig D word seen random D.initialConfiguration) (4 * t)
      (decisionConfig D word seen random c) ∧ D.TapeGeometry c := by
  induction path with
  | refl =>
      refine ⟨.refl _ ?_, D.initialConfiguration_geometry⟩
      exact (decisionConfig_bounded D word seen random s _ (by simp [Machine.initialConfiguration])
        (by simp [Machine.initialConfiguration])).mono _ (by omega)
  | @tail t current next path step ih =>
      have bounds := space.steps_decisionView_bounded D path
      have input : current.inputHead ≤ word.length := bounds.inputHead
      have work : current.workHead.natAbs ≤ s := bounds.workHead
      cases action : D.transition current.state word[current.inputHead]? none none
          (current.work current.workHead) with
      | accept => simp [Machine.next, decisionData, action] at step
      | reject => simp [Machine.next, decisionData, action] at step
      | readRandom no yes =>
          have impossible := deterministic current.state word[current.inputHead]? none none
            (current.work current.workHead)
          rw [action] at impossible
          exact False.elim impossible
      | step state write workMove inputMove auxiliary index emit =>
          have actual : D.transition current.state (decisionData word).input[current.inputHead]?
              (decisionData word).auxiliary[current.auxiliaryHead]?
              (if current.indexHead < (decisionData word).index then some () else none)
              (current.work current.workHead) =
              .step state write workMove inputMove auxiliary index emit := by
            simpa [decisionData] using action
          rw [D.next_step _ [] current _ _ _ _ _ _ _ actual] at step
          cases step
          have block := (decision_step D word seen random bits current input ih.2.head
            state write workMove inputMove auxiliary index emit action).inRegion (bank D)
              (word.length + s) (decisionConfig_bounded D word seen random s current input work)
          refine ⟨?_, D.stepConfiguration_geometry _ _ ih.2 _ _ _ _ _ _ _⟩
          simpa [Nat.mul_add, Nat.mul_one] using ih.1.trans (bank D) block

/-- Compile the entire decision into the original finite-control machine.
Its physical visited region remains bounded even for an exponentially long
source computation. The caller supplies the bank-ready configuration because
the candidate word has already been loaded. -/
theorem decision_native_inRegion (deterministic : D.Deterministic)
    (word : List α) (seen : Bool) (random s : ℕ) (bits : BitString)
    (space : D.SpaceBound (decisionData word) s) {t : ℕ} {c : Configuration D}
    (path : D.Steps (decisionData word) [] D.initialConfiguration t c)
    (negative : Fin 2 → Bool) (start : Configuration (machine D))
    (ready : TransducerBank.BankReady (bank D)
      (decisionConfig D word seen random D.initialConfiguration) negative start)
    (region : (machine D).InRegion (word.length + s + 4) start) :
    ∃ ticks finish sides,
      TransducerBank.BankReady (bank D) (decisionConfig D word seen random c) sides finish ∧
      (machine D).Steps (generatorData word.length) bits start ticks finish ∧
      (machine D).InRegion (word.length + s + 4) finish :=
  (decision_steps_inRegion D deterministic word seen random s bits space path).1.compile
    (bank D) negative start ready region

end
end ComplexityOfGenerators.Simulation.CyclicGenerator
