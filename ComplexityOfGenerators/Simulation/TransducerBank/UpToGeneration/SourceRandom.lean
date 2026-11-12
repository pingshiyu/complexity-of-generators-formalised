import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.SourceStep

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

@[simp] theorem configuration_choose (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (no yes : Q) (bit : Bool) :
    TapeBank.choose (inspecting B fallback word offset source) (if bit then .fetch yes else .fetch no) =
      configuration B fallback word offset (TapeBank.choose source (if bit then yes else no)) := by
  cases bit <;> simp [TapeBank.choose, inspecting, configuration, Nat.add_assoc]

theorem random_path (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (no yes : Q)
    (action : B.instruction (decisionData word) source = .readRandom no yes)
    (bit : Bool) (lookup : (bits.drop offset)[source.randomHead]? = some bit) :
    (bank B fallback).Steps (generatorData n) bits (configuration B fallback word offset source) 2
      (configuration B fallback word offset (TapeBank.choose source (if bit then yes else no))) := by
  have first := fetch_step B fallback n bits word offset source
  have instruction : (bank B fallback).instruction (generatorData n)
      (inspecting B fallback word offset source) = .readRandom (.fetch no) (.fetch yes) := by
    rw [inspect_instruction B fallback n word offset source, action]
  have second : (bank B fallback).Steps (generatorData n) bits
      (inspecting B fallback word offset source) 1
      (configuration B fallback word offset (TapeBank.choose source (if bit then yes else no))) := by
    apply TapeBank.Steps.random (B := bank B fallback) _ (.fetch no) (.fetch yes) bit 0 _ instruction
      (by simpa only [List.getElem?_drop, inspecting, configuration] using lookup)
    rw [configuration_choose]
    exact .refl _
  exact first.trans (bank B fallback) second

theorem exhausted_executes (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) (no yes : Q)
    (action : B.instruction (decisionData word) source = .readRandom no yes)
    (absent : (bits.drop offset)[source.randomHead]? = none) :
    (bank B fallback).Executes (generatorData n) bits (configuration B fallback word offset source) 1 .exhausted := by
  have first := fetch_step B fallback n bits word offset source
  have instruction : (bank B fallback).instruction (generatorData n)
      (inspecting B fallback word offset source) = .readRandom (.fetch no) (.fetch yes) := by
    rw [inspect_instruction B fallback n word offset source, action]
  exact first.executes (bank B fallback) (.exhausted _ (.fetch no) (.fetch yes) instruction
    (by simpa only [List.getElem?_drop, inspecting, configuration] using absent))

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
