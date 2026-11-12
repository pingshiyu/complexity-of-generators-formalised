import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceExecution
import ComplexityOfGenerators.Simulation.TransducerBank.RegionBounds

/-! Source simulation in a fixed work region. Each three-step macro starts
with source heads in the original region. The final replay/fallback has cost
linear in the word and fixed fallback, so its elementary time bound also gives
a space bound independent of the source running time. -/
namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α Q S : Type} {k : ℕ} [Fintype α]
    (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

def sourceRadius (word : Word α) (radius : ℕ) : ℕ :=
  max radius word.length+2*word.length+fallback.length+3

theorem configuration_bounded (n : ℕ) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (radius : ℕ)
    (bounded : B.Bounded (decisionData word) radius source) :
    (bank B fallback).Bounded (generatorData n) (max radius word.length)
      (configuration B fallback word offset source) := by
  refine ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,?_⟩
  intro j
  refine Fin.lastCases ?_ (fun j=>?_) j
  · simpa only [configuration,Fin.lastCases_last,Int.natAbs_natCast] using bounded.input.trans (Nat.le_max_right radius word.length)
  · simpa only [configuration,Fin.lastCases_castSucc] using (bounded.head j).trans (Nat.le_max_left radius word.length)

/-- The region does not grow with the number of source instructions. -/
theorem source_regionRun (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    {source : BankConfiguration Unit Q S k} {ticks : ℕ} {result : Outcome Unit}
    (execution : B.Executes (decisionData word) (bits.drop offset) source ticks result) (radius : ℕ)
    (allBound : ∀ time finish, B.Steps (decisionData word) (bits.drop offset) source time finish →
      B.Bounded (decisionData word) radius finish) :
    (bank B fallback).RegionRun (generatorData n) bits (sourceRadius fallback word radius)
      (configuration B fallback word offset source) (sourceOutcome word fallback result) := by
  induction execution with
  | accept source action =>
    have bound := allBound 0 source (.refl _)
    have inputBound : source.inputHead≤word.length := bound.input
    have actual := source_accept_executes B fallback n bits word offset source action
    exact (actual.inRegion (bank B fallback) (configuration_bounded B fallback n word offset source radius bound)).mono
      (bank B fallback) (by dsimp [sourceRadius];omega)
  | reject source action =>
    have bound := allBound 0 source (.refl _)
    have actual := source_reject_executes B fallback n bits word offset source action
    exact (actual.inRegion (bank B fallback) (configuration_bounded B fallback n word offset source radius bound)).mono
      (bank B fallback) (by dsimp [sourceRadius];omega)
  | exhausted source no yes action absent =>
    have bound := allBound 0 source (.refl _)
    have actual := exhausted_executes B fallback n bits word offset source no yes action absent
    exact (actual.inRegion (bank B fallback) (configuration_bounded B fallback n word offset source radius bound)).mono
      (bank B fallback) (by dsimp [sourceRadius];omega)
  | random source no yes bit ticks result action lookup rest ih =>
    have bound := allBound 0 source (.refl _)
    have nextAll : ∀ time finish,
        B.Steps (decisionData word) (bits.drop offset) (TapeBank.choose source (if bit then yes else no)) time finish →
          B.Bounded (decisionData word) radius finish :=
      fun time finish path => allBound (time+1) finish (.random source no yes bit time finish action lookup path)
    have remaining := ih nextAll
    have path := (random_path B fallback n bits word offset source no yes action bit lookup).inRegion
      (bank B fallback) (max radius word.length) (configuration_bounded B fallback n word offset source radius bound)
    exact remaining.prepend (bank B fallback) (path.mono (bank B fallback) (by dsimp [sourceRadius];omega))
  | step source next write work input auxiliary index emit ticks result action rest ih =>
    have bound := allBound 0 source (.refl _)
    have nextAll : ∀ time finish,
        B.Steps (decisionData word) (bits.drop offset)
          (B.advance (decisionData word) source next write work input auxiliary index emit) time finish →
          B.Bounded (decisionData word) radius finish :=
      fun time finish path => allBound (time+1) finish (.step source next write work input auxiliary index emit time finish action path)
    have remaining := ih nextAll
    have path := (step_path B fallback n bits word offset source bound.input next write work input auxiliary index emit action).inRegion
      (bank B fallback) (max radius word.length) (configuration_bounded B fallback n word offset source radius bound)
    exact remaining.prepend (bank B fallback) (path.mono (bank B fallback) (by dsimp [sourceRadius];omega))

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
