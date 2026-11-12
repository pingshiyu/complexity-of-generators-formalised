import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.OutputBasic

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

theorem fallback_step (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (position : ℕ) (live : position < fallback.length) :
    (bank B fallback).Steps (generatorData n) bits
      (outputConfiguration B fallback word offset source source.inputHead
        (.fallback ⟨position, by omega⟩) (fallback.take position)) 1
      (outputConfiguration B fallback word offset source source.inputHead
        (.fallback ⟨position + 1, by omega⟩) (fallback.take (position + 1))) := by
  have printed : fallback.take position ++ [fallback[position]] = fallback.take (position + 1) :=
    (List.take_succ_eq_append_getElem live).symm
  have instruction : (bank B fallback).instruction (generatorData n)
      (outputConfiguration B fallback word offset source source.inputHead
        (.fallback ⟨position, by omega⟩) (fallback.take position)) =
      .step (.fallback ⟨position + 1, by omega⟩) (wordTape B word source.inputHead)
        .stay .stay .stay .stay (some fallback[position]) := by
    simp [TapeBank.instruction, bank, outputConfiguration, configuration, generatorData, live]
  have actual := TapeBank.Steps.single (bank B fallback) (generatorData n) bits _ _ _ _ _ _ _ _ instruction
  have same : (bank B fallback).advance (generatorData n)
      (outputConfiguration B fallback word offset source source.inputHead
        (.fallback ⟨position, by omega⟩) (fallback.take position))
      (.fallback ⟨position + 1, by omega⟩) (wordTape B word source.inputHead)
        .stay .stay .stay .stay (some fallback[position]) =
      outputConfiguration B fallback word offset source source.inputHead
        (.fallback ⟨position + 1, by omega⟩) (fallback.take (position + 1)) := by
    apply BankConfiguration.ext <;>
      simp only [TapeBank.advance, outputConfiguration, configuration, bank, generatorData,
        Move.onInput, Nat.zero_min, Option.toList_some]
    · exact printed
    · rw [Fin.lastCases_last, Move.onInt, Fuel.lastCases_update_last]
    · rw [Fin.lastCases_last, Fin.lastCases_last, Function.update_eq_self,
        Fuel.lastCases_update_last]
  simpa only [same] using actual

/-- A rejected source branch emits the fixed fallback using its literal finite
control table. No word is supplied to the machine as an oracle operation. -/
theorem fallback_executes (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (remaining position : ℕ)
    (capacity : position + remaining = fallback.length) :
    (bank B fallback).Executes (generatorData n) bits
      (outputConfiguration B fallback word offset source source.inputHead
        (.fallback ⟨position, by omega⟩) (fallback.take position)) remaining (.accepted fallback) := by
  induction remaining generalizing position with
  | zero =>
    have ended : position = fallback.length := by omega
    subst position
    have instruction : (bank B fallback).instruction (generatorData n)
        (outputConfiguration B fallback word offset source source.inputHead
          (.fallback ⟨fallback.length, by omega⟩) (fallback.take fallback.length)) = .accept := by
      simp [TapeBank.instruction, bank, outputConfiguration, configuration, generatorData]
    simpa [outputConfiguration] using TapeBank.Executes.accept (B := bank B fallback) _ instruction
  | succ remaining ih =>
    have step := fallback_step B fallback n bits word offset source position (by omega)
    have rest := ih (position + 1) (by omega)
    simpa only [Nat.add_comm 1 remaining] using step.executes (bank B fallback) rest

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
