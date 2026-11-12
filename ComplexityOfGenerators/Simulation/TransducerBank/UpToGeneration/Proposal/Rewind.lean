import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

 theorem rewind_region (n : ℕ) (bits : BitString) (word : Word α) (consumed position : ℕ)
    (within : position≤n) :
    (bank B fallback).RegionSteps (generatorData n) bits n
      (configuration B fallback word consumed position .guessRewind) (position+1)
      (configuration B fallback word consumed 0 (.fetch B.initial)) := by
  induction position with
  | zero =>
      apply TapeBank.RegionSteps.step _ (.fetch B.initial) (wordTape B word 0)
        .stay .stay .stay .stay none 0 _ (bounded B fallback n word consumed 0 _ (by omega))
      · simp [TapeBank.instruction,configuration,bank]
      · have cell : wordTape B word 0=
            (configuration B fallback word consumed 0 .guessRewind).tape ((bank B fallback).select .guessRewind)
              ((configuration B fallback word consumed 0 .guessRewind).head ((bank B fallback).select .guessRewind)) := by
          simp only [configuration,bank,Fin.lastCases_last,Nat.cast_zero]
        rw [cell,advance_stay B fallback n word consumed 0 _ _ (by omega)]
        exact .refl _ (bounded B fallback n word consumed 0 _ (by omega))
  | succ position ih =>
      have table : (bank B fallback).instruction (generatorData n)
          (configuration B fallback word consumed (position+1) .guessRewind)=
          .step .guessRewind (wordTape B word (position+1)) .left .stay .stay .left none := by
        simp only [TapeBank.instruction,configuration,bank,Fin.lastCases_last]
        simp
        omega
      apply TapeBank.RegionSteps.step _ .guessRewind _ .left .stay .stay .left none (position+1) _
        (bounded B fallback n word consumed (position+1) _ within) table
      have advanced : (bank B fallback).advance (generatorData n)
          (configuration B fallback word consumed (position+1) .guessRewind) .guessRewind
          (wordTape B word (position+1)) .left .stay .stay .left none=
          configuration B fallback word consumed position .guessRewind := by
        apply BankConfiguration.ext <;> try rfl
        case head =>
          simp only [TapeBank.advance,configuration,bank,Fin.lastCases_last,Fuel.lastCases_update_last,Move.onInt]
          simp
        case tape =>
          simp only [TapeBank.advance,configuration,bank,Fin.lastCases_last,Nat.cast_add,Nat.cast_one,
            Function.update_eq_self,Fuel.lastCases_update_last]
      rw [advanced]
      exact ih (by omega)

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal
