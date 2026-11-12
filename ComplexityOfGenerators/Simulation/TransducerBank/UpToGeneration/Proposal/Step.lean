import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal.Rewind

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

 theorem go_last (n : ℕ) (bits : BitString) (word : Word α) (consumed position : ℕ)
    (state next : Control B fallback) (within : position≤n)
    (selected : (bank B fallback).select state=Fin.last k)
    (table : (bank B fallback).instruction (generatorData n) (configuration B fallback word consumed position state)=
      .step next (wordTape B word position) .stay .stay .stay .stay none) :
    (bank B fallback).RegionSteps (generatorData n) bits n (configuration B fallback word consumed position state) 1
      (configuration B fallback word consumed position next) := by
  apply TapeBank.RegionSteps.step _ next _ .stay .stay .stay .stay none 0 _
    (bounded B fallback n word consumed position state within) table
  have cell : wordTape B word position=
      (configuration B fallback word consumed position state).tape ((bank B fallback).select state)
        ((configuration B fallback word consumed position state).head ((bank B fallback).select state)) := by
    simp only [configuration,selected,Fin.lastCases_last]
  rw [cell,advance_stay B fallback n word consumed position state next within]
  exact .refl _ (bounded B fallback n word consumed position next within)

 theorem random_step (n : ℕ) (bits : BitString) (word : Word α) (consumed position : ℕ)
    (state no yes : Control B fallback) (bit : Bool) (within : position≤n)
    (table : (bank B fallback).instruction (generatorData n) (configuration B fallback word consumed position state)=
      .readRandom no yes) (lookup : bits[consumed]?=some bit) :
    (bank B fallback).RegionSteps (generatorData n) bits n (configuration B fallback word consumed position state) 1
      (configuration B fallback word (consumed+1) position (if bit then yes else no)) := by
  apply TapeBank.RegionSteps.random _ no yes bit 0 _ (bounded B fallback n word consumed position state within) table lookup
  rw [choose_configuration]
  exact .refl _ (bounded B fallback n word (consumed+1) position _ within)

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Proposal
