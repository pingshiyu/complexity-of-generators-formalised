import ComplexityOfGenerators.Simulation.AuxiliaryDecision
import ComplexityOfGenerators.Simulation.CompositionExecution

/-! The decision adapter discards its source output.  The shared sampler/
recoverer composition therefore leaves its own output unchanged. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool α) (M : Machine α Bool Unit)

theorem auxiliaryComposition_step_no_output (q : CompositionState S (auxiliaryDecision M))
    (index : Option Unit) (origin : Bool) (cell : CompositionSymbol S (auxiliaryDecision M))
    (next write work input auxiliary idx emit)
    (table : compositionTransition S (auxiliaryDecision M) q index origin cell =
      .step next write work input auxiliary idx emit) : emit = none := by
  cases q
  case recoverWork q idx certificate =>
    cases action : M.transition q certificate none none cell.recoverer <;>
      simp only [compositionTransition, auxiliaryDecision, action] at table
    all_goals repeat' split at table
    all_goals simp_all
  all_goals simp only [compositionTransition] at table
  all_goals repeat' split at table
  all_goals simp_all

theorem auxiliaryComposition_output_preserved {n : ℕ} {bits : BitString}
    {c d : CompositionConfiguration S (auxiliaryDecision M)} {t : ℕ}
    (path : (samplerCompositionBank S (auxiliaryDecision M)).Steps (generatorData n) bits c t d) :
    d.output = c.output := by
  induction path with
  | refl => rfl
  | random c no yes letter t d table lookup rest ih => exact ih
  | step c next write work input auxiliary index emit t d table rest ih =>
      have absent := auxiliaryComposition_step_no_output S M _ _ _ _ _ _ _ _ _ _ _ table
      simpa [TransducerBank.TapeBank.advance, absent] using ih

end
end ComplexityOfGenerators.Simulation
