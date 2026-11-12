import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceRandom
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Output
import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Fallback

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

/-- Accepted source branches replay the actual guessed input. Source output
symbols are Unit and play no role in decision acceptance. -/
theorem source_accept_executes (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k)
    (action : B.instruction (decisionData word) source = .accept) :
    (bank B fallback).Executes (generatorData n) bits (configuration B fallback word offset source)
      (source.inputHead + word.length + 3) (.accepted word) := by
  have first := fetch_step B fallback n bits word offset source
  have second : (bank B fallback).Steps (generatorData n) bits (inspecting B fallback word offset source) 1
      (outputConfiguration B fallback word offset source source.inputHead .acceptRewind []) := by
    apply TapeBank.Steps.go (bank B fallback) (generatorData n) bits _ .acceptRewind
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    rw [inspect_instruction B fallback n word offset source, action]
    simp [inspecting, configuration, bank]
  have last := accepted_output B fallback n bits word offset source source.inputHead
  have actual := (first.trans (bank B fallback) second).executes (bank B fallback) last
  have size : 1 + 1 + (source.inputHead + 1 + word.length) = source.inputHead + word.length + 3 := by omega
  simpa only [size] using actual

/-- Rejected source branches emit a fixed finite literal, converting source
rejection into successful generation rather than exposing explicit rejection. -/
theorem source_reject_executes (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k)
    (action : B.instruction (decisionData word) source = .reject) :
    (bank B fallback).Executes (generatorData n) bits (configuration B fallback word offset source)
      (fallback.length + 2) (.accepted fallback) := by
  have first := fetch_step B fallback n bits word offset source
  have second : (bank B fallback).Steps (generatorData n) bits (inspecting B fallback word offset source) 1
      (outputConfiguration B fallback word offset source source.inputHead (.fallback 0) []) := by
    apply TapeBank.Steps.go (bank B fallback) (generatorData n) bits _ (.fallback 0)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    rw [inspect_instruction B fallback n word offset source, action]
    simp [inspecting, configuration, bank]
  have last := fallback_executes B fallback n bits word offset source fallback.length 0 (by omega)
  have actual := (first.trans (bank B fallback) second).executes (bank B fallback) last
  simpa only [Nat.zero_add, List.take_zero, Nat.add_comm 2 fallback.length] using actual

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
