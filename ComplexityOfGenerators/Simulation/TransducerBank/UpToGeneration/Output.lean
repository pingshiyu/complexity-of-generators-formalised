import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.OutputBasic

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

theorem emit_executes (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (remaining position : ℕ)
    (capacity : position + remaining = word.length) :
    (bank B fallback).Executes (generatorData n) bits
      (outputConfiguration B fallback word offset source position .emit (word.take position)) remaining
      (.accepted word) := by
  induction remaining generalizing position with
  | zero =>
      have ended : position = word.length := by omega
      subst position
      have instruction : (bank B fallback).instruction (generatorData n)
          (outputConfiguration B fallback word offset source word.length .emit (word.take word.length)) = .accept := by
        simp [TapeBank.instruction, bank, outputConfiguration, configuration, generatorData]
      simpa [outputConfiguration] using TapeBank.Executes.accept (B := bank B fallback) _ instruction
  | succ remaining ih =>
      have step := emit_step B fallback n bits word offset source position (by omega)
      have rest := ih (position + 1) (by omega)
      simpa only [Nat.add_comm 1 remaining] using step.executes (bank B fallback) rest

theorem output_rewind_path (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (position : ℕ) :
    (bank B fallback).Steps (generatorData n) bits
      (outputConfiguration B fallback word offset source position .acceptRewind []) position
      (outputConfiguration B fallback word offset source 0 .acceptRewind []) := by
  induction position with
  | zero => exact .refl _
  | succ position ih =>
      have step := output_rewind_step B fallback n bits word offset source position
      simpa only [Nat.add_comm 1 position] using step.trans (bank B fallback) ih

/-- Source acceptance replays the actual immutable input word, without storing
or copying that word in finite control. -/
theorem accepted_output (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (position : ℕ) :
    (bank B fallback).Executes (generatorData n) bits
      (outputConfiguration B fallback word offset source position .acceptRewind [])
      (position + 1 + word.length) (.accepted word) := by
  have first := output_rewind_path B fallback n bits word offset source position
  have second : (bank B fallback).Steps (generatorData n) bits
      (outputConfiguration B fallback word offset source 0 .acceptRewind []) 1
      (outputConfiguration B fallback word offset source 0 .emit []) := by
    apply TapeBank.Steps.go (bank B fallback) (generatorData n) bits _ .emit
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    simp [TapeBank.instruction, bank, outputConfiguration, configuration, generatorData]
  have last := emit_executes B fallback n bits word offset source word.length 0 (by omega)
  exact (first.trans (bank B fallback) second).executes (bank B fallback) last

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
