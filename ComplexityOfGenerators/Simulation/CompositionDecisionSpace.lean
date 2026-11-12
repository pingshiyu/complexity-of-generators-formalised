import ComplexityOfGenerators.Simulation.AuxiliaryDecision
import ComplexityOfGenerators.Simulation.CompositionRecovererSteps
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps
import ComplexityOfGenerators.Foundations.SpaceReachability

/-! A deterministic decision branch can take arbitrarily long while the
sampler/recoverer bank remains in one fixed work region. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (D : Machine α Bool Unit)

def auxiliaryDecisionAt (random : ℕ) (c : Configuration D) : Configuration (auxiliaryDecision D) :=
  {auxiliaryDecisionConfiguration D c with randomHead := random}

theorem compositionDecision_bounded (n : ℕ) (word : List α)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ)
    (random s : ℕ) (c : Configuration D)
    (input : c.inputHead ≤ word.length) (work : c.workHead.natAbs ≤ s) :
    (samplerCompositionBank S (auxiliaryDecision D)).Bounded (generatorData n)
      (n + word.length + samplerHead.natAbs + s)
      (recovererBankConfiguration S (auxiliaryDecision D) n word samplerWork samplerHead (auxiliaryDecisionAt D random c)) := by
  constructor
  · simp [recovererBankConfiguration, generatorData]
  · simp [recovererBankConfiguration, generatorData]
  · simp [recovererBankConfiguration, generatorData]
  · intro j
    fin_cases j <;> simp [recovererBankConfiguration, auxiliaryDecisionAt, auxiliaryDecisionConfiguration] <;> omega

theorem compositionDecision_step (n : ℕ) (word : List α) (bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (random : ℕ)
    (c : Configuration D) (inputBound : c.inputHead ≤ word.length)
    (state : Fin D.states) (write : Option (Fin D.symbols)) (work input auxiliary index : Move) (emit : Option Unit)
    (action : D.transition c.state word[c.inputHead]? none none (c.work c.workHead) =
      .step state write work input auxiliary index emit) :
    (samplerCompositionBank S (auxiliaryDecision D)).Steps (generatorData n) bits
      (recovererBankConfiguration S (auxiliaryDecision D) n word samplerWork samplerHead (auxiliaryDecisionAt D random c)) 5
      (recovererBankConfiguration S (auxiliaryDecision D) n word samplerWork samplerHead
        (auxiliaryDecisionAt D random (D.stepConfiguration (decisionData word) c state write work input auxiliary index emit))) := by
  let R := auxiliaryDecision D
  let current := auxiliaryDecisionAt D random c
  have adapted : R.transition current.state none word[current.auxiliaryHead]?
      (if current.indexHead < n then some () else none) (current.work current.workHead) =
      .step state write work .stay input .stay none := by
    simp [R, current, auxiliaryDecisionAt, auxiliaryDecisionConfiguration, auxiliaryDecision, action]
  have first := composition_recoverer_fetch S R n word bits samplerWork samplerHead current
  have second := composition_recoverer_step S R n word bits samplerWork samplerHead current
    (by simp [current, auxiliaryDecisionAt, auxiliaryDecisionConfiguration])
    (by simpa [current, auxiliaryDecisionAt, auxiliaryDecisionConfiguration] using inputBound)
    state write work .stay input .stay none adapted
  have equal : R.stepConfiguration (certificateData n word) current state write work .stay input .stay none =
      auxiliaryDecisionAt D random (D.stepConfiguration (decisionData word) c state write work input auxiliary index emit) := by
    cases write <;>
      simp [current, auxiliaryDecisionAt, auxiliaryDecisionConfiguration, Machine.stepConfiguration,
        certificateData, decisionData, Move.onInput]
  rw [equal] at second
  exact first.trans _ second

theorem compositionDecision_steps_inRegion (deterministic : D.Deterministic)
    (n : ℕ) (word : List α) (bits : BitString)
    (samplerWork : ℤ → Option (Fin S.symbols)) (samplerHead : ℤ) (random s : ℕ)
    (space : D.SpaceBound (decisionData word) s) {t : ℕ} {c : Configuration D}
    (path : D.Steps (decisionData word) [] D.initialConfiguration t c) :
    (samplerCompositionBank S (auxiliaryDecision D)).RegionSteps (generatorData n) bits
      (n + word.length + samplerHead.natAbs + s + 5)
      (recovererBankConfiguration S (auxiliaryDecision D) n word samplerWork samplerHead
        (auxiliaryDecisionAt D random D.initialConfiguration)) (5 * t)
      (recovererBankConfiguration S (auxiliaryDecision D) n word samplerWork samplerHead
        (auxiliaryDecisionAt D random c)) := by
  induction path with
  | refl =>
      apply TransducerBank.TapeBank.RegionSteps.refl
      exact (compositionDecision_bounded S D n word samplerWork samplerHead random s _
        (by simp [Machine.initialConfiguration]) (by simp [Machine.initialConfiguration])).mono _ (by omega)
  | @tail t current next path step ih =>
      have bounds := space.steps_decisionView_bounded D path
      have inputBound : current.inputHead ≤ word.length := bounds.inputHead
      have workBound : current.workHead.natAbs ≤ s := bounds.workHead
      cases action : D.transition current.state word[current.inputHead]? none none (current.work current.workHead) with
      | accept => simp [Machine.next, decisionData, action] at step
      | reject => simp [Machine.next, decisionData, action] at step
      | readRandom no yes =>
          have impossible := deterministic current.state word[current.inputHead]? none none (current.work current.workHead)
          simp [action] at impossible
      | step state write work input auxiliary index emit =>
          rw [D.next_step _ [] current state write work input auxiliary index emit (by simpa [decisionData] using action)] at step
          cases step
          have block := (compositionDecision_step S D n word bits samplerWork samplerHead random current inputBound
            state write work input auxiliary index emit action).inRegion _
              (n + word.length + samplerHead.natAbs + s)
              (compositionDecision_bounded S D n word samplerWork samplerHead random s current inputBound workBound)
          simpa [Nat.mul_add, Nat.mul_one] using ih.trans _ block

end
end ComplexityOfGenerators.Simulation
