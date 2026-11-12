import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceTerminal

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

def sourceOutcome (word fallback : Word α) : Outcome Unit → Outcome α
  | .accepted _ => .accepted word
  | .rejected => .accepted fallback
  | .exhausted => .exhausted

/-- Simulate a complete finite source branch, including actual guessed-word
replay or finite fallback emission. Source choice bits begin at the real cursor
after the proposal; neither the proposal nor source bits are resampled. -/
theorem source_executes (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    {source : BankConfiguration Unit Q S k} {ticks : ℕ} {result : Outcome Unit}
    (execution : B.Executes (decisionData word) (bits.drop offset) source ticks result)
    (bounded : source.inputHead ≤ word.length) :
    ∃ targetTicks, targetTicks ≤ 3 * ticks + 2 * word.length + fallback.length + 3 ∧
      (bank B fallback).Executes (generatorData n) bits (configuration B fallback word offset source)
        targetTicks (sourceOutcome word fallback result) := by
  induction execution with
  | accept source action =>
      exact ⟨source.inputHead + word.length + 3, by omega,
        source_accept_executes B fallback n bits word offset source action⟩
  | reject source action =>
      exact ⟨fallback.length + 2, by omega,
        source_reject_executes B fallback n bits word offset source action⟩
  | exhausted source no yes action absent =>
      exact ⟨1, by omega, exhausted_executes B fallback n bits word offset source no yes action absent⟩
  | random source no yes bit ticks result action lookup rest ih =>
      obtain ⟨targetTicks, cost, simulated⟩ := ih bounded
      have path := random_path B fallback n bits word offset source no yes action bit lookup
      exact ⟨2 + targetTicks, by omega, path.executes (bank B fallback) simulated⟩
  | step source next write work input auxiliary index emit ticks result action rest ih =>
      obtain ⟨targetTicks, cost, simulated⟩ := ih
        (input.onInput_le word.length source.inputHead bounded)
      have path := step_path B fallback n bits word offset source bounded next write work
        input auxiliary index emit action
      exact ⟨3 + targetTicks, by omega, path.executes (bank B fallback) simulated⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
