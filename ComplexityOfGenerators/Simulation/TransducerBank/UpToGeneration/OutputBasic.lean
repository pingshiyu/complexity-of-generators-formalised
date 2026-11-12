import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceBasic

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

def outputConfiguration (word : Word α) (offset : ℕ) (source : BankConfiguration Unit Q S k)
    (position : ℕ) (phase : Control B fallback) (emitted : Word α) :
    BankConfiguration α (Control B fallback) (Cell S α) (k + 1) :=
  {configuration B fallback word offset source with
    state := phase
    head := Fin.lastCases (position : ℤ) source.head
    output := emitted}

/-- One emitted letter is one actual bank transition; the guessed input and all
source tapes are preserved, including the current cell. -/
theorem emit_step (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (position : ℕ) (live : position < word.length) :
    (bank B fallback).Steps (generatorData n) bits
      (outputConfiguration B fallback word offset source position .emit (word.take position)) 1
      (outputConfiguration B fallback word offset source (position + 1) .emit (word.take (position + 1))) := by
  have printed : word.take position ++ [word[position]] = word.take (position + 1) :=
    (List.take_succ_eq_append_getElem live).symm
  have instruction : (bank B fallback).instruction (generatorData n)
      (outputConfiguration B fallback word offset source position .emit (word.take position)) =
      .step .emit (wordTape B word position) .right .stay .stay .stay (some word[position]) := by
    simp [TapeBank.instruction, bank, outputConfiguration, configuration, generatorData,
      List.getElem?_eq_getElem live]
  have actual := TapeBank.Steps.single (bank B fallback) (generatorData n) bits _ _ _ _ _ _ _ _ instruction
  have same : (bank B fallback).advance (generatorData n)
      (outputConfiguration B fallback word offset source position .emit (word.take position))
      .emit (wordTape B word position) .right .stay .stay .stay (some word[position]) =
      outputConfiguration B fallback word offset source (position + 1) .emit (word.take (position + 1)) := by
    apply BankConfiguration.ext <;>
      simp only [TapeBank.advance, outputConfiguration, configuration, bank, generatorData,
        Move.onInput, Nat.zero_min, Option.toList_some]
    · exact printed
    · rw [Fin.lastCases_last, Move.onInt, Fuel.lastCases_update_last]
      congr 1
    · rw [Fin.lastCases_last, Fin.lastCases_last, Function.update_eq_self,
        Fuel.lastCases_update_last]
  simpa only [same] using actual

theorem output_rewind_step (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (position : ℕ) :
    (bank B fallback).Steps (generatorData n) bits
      (outputConfiguration B fallback word offset source (position + 1) .acceptRewind []) 1
      (outputConfiguration B fallback word offset source position .acceptRewind []) := by
  have instruction : (bank B fallback).instruction (generatorData n)
      (outputConfiguration B fallback word offset source (position + 1) .acceptRewind []) =
      .step .acceptRewind (wordTape B word (position + 1)) .left .stay .stay .stay none := by
    simp [TapeBank.instruction, bank, outputConfiguration, configuration, generatorData] <;> omega
  have actual := TapeBank.Steps.single (bank B fallback) (generatorData n) bits _ _ _ _ _ _ _ _ instruction
  have same : (bank B fallback).advance (generatorData n)
      (outputConfiguration B fallback word offset source (position + 1) .acceptRewind [])
      .acceptRewind (wordTape B word (position + 1)) .left .stay .stay .stay none =
      outputConfiguration B fallback word offset source position .acceptRewind [] := by
    apply BankConfiguration.ext <;>
      simp only [TapeBank.advance, outputConfiguration, configuration, bank, generatorData,
        Move.onInput, Nat.zero_min, Option.toList_none, List.append_nil]
    · rw [Fin.lastCases_last, Move.onInt, Fuel.lastCases_update_last]
      congr 1
      omega
    · rw [Fin.lastCases_last, Fin.lastCases_last]
      simp only [Nat.cast_add, Nat.cast_one]
      rw [Function.update_eq_self, Fuel.lastCases_update_last]
  simpa only [same] using actual

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
