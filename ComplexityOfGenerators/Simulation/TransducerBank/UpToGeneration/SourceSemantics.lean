import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceExecution
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Machine

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (source : MultitapeMachine α Bool Unit) (fallback : Word α)

/-- A bounded decider branch gives an actual bounded execution from the proposal
endpoint, including physical replay/fallback output. -/
theorem source_bounded (n : ℕ) (bits : BitString) (word : Word α) (offset time : ℕ)
    (bounded : source.TimeBound (decisionData word) time) :
    ∃ ticks result, ticks ≤ 3 * time + 2 * word.length + fallback.length + 3 ∧
      (bank source.program fallback).Executes (generatorData n) bits
        (configuration source.program fallback word offset source.initialConfiguration) ticks result := by
  obtain ⟨sourceTicks, result, cost, execution⟩ := bounded (bits.drop offset)
  obtain ⟨ticks, actualCost, actual⟩ :=
    source_executes source.program fallback n bits word offset execution (Nat.zero_le _)
  exact ⟨ticks, sourceOutcome word fallback result, by omega, actual⟩

/-- Correctness uses the source's real accepting branch or the fixed known
member. The generator never tests language membership as a primitive. -/
theorem source_result_sound (language : Language α)
    (recognizes : ∀ word, (∃ bits, source.Accepts (decisionData word) bits) ↔ word ∈ language)
    (fallbackMember : fallback ∈ language)
    (n : ℕ) (word output : Word α) (wordSmall : word.length ≤ n) (fallbackSmall : fallback.length ≤ n)
    (bits : BitString) (ticks : ℕ) (result : Outcome Unit)
    (execution : source.Executes (decisionData word) bits source.initialConfiguration ticks result)
    (accepted : sourceOutcome word fallback result = .accepted output) :
    output ∈ language ∧ output.length ≤ n := by
  cases result with
  | accepted witness =>
      have same : word = output := Outcome.accepted.inj accepted
      rw [← same]
      exact ⟨(recognizes word).mp ⟨bits, witness, ticks, execution⟩, wordSmall⟩
  | rejected =>
      have same : fallback = output := Outcome.accepted.inj accepted
      rw [← same]
      exact ⟨fallbackMember, fallbackSmall⟩
  | exhausted => cases accepted

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
