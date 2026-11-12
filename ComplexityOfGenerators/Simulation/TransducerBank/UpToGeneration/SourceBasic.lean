import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.WordTape
import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} [Fintype α]
  (B : TapeBank α Bool Unit Q S k) (fallback : Word α)

/-- Source output is irrelevant to decision acceptance. The guessed input is
real immutable tape data; all source work tapes remain separate. -/
def configuration (word : Word α) (offset : ℕ) (source : BankConfiguration Unit Q S k) :
    BankConfiguration α (Control B fallback) (Cell S α) (k + 1) :=
  ⟨.fetch source.state, 0, 0, 0, offset + source.randomHead, [],
    Fin.lastCases (source.inputHead : ℤ) source.head,
    Fin.lastCases (wordTape B word) (fun j p => (source.tape j p, none))⟩

def inspecting (word : Word α) (offset : ℕ) (source : BankConfiguration Unit Q S k) :
    BankConfiguration α (Control B fallback) (Cell S α) (k + 1) :=
  {configuration B fallback word offset source with
    state := .inspect source.state (decide (source.head (B.select source.state) = 0))
      (source.tape (B.select source.state) (source.head (B.select source.state)))}

theorem fetch_step (n : ℕ) (bits : BitString) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) :
    (bank B fallback).Steps (generatorData n) bits (configuration B fallback word offset source) 1
      (inspecting B fallback word offset source) := by
  apply TapeBank.Steps.go (bank B fallback) (generatorData n) bits _ _
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  simp [TapeBank.instruction, bank, configuration, generatorData]

theorem inspect_instruction (n : ℕ) (word : Word α) (offset : ℕ)
    (source : BankConfiguration Unit Q S k) :
    (bank B fallback).instruction (generatorData n) (inspecting B fallback word offset source) =
      match B.instruction (decisionData word) source with
      | .accept => .step .acceptRewind (wordTape B word source.inputHead) .stay .stay .stay .stay none
      | .reject => .step (.fallback 0) (wordTape B word source.inputHead) .stay .stay .stay .stay none
      | .readRandom no yes => .readRandom (.fetch no) (.fetch yes)
      | .step next write work input _ _ _ =>
          .step (.commit (B.select source.state) next write work) (wordTape B word source.inputHead)
            (inputMove input (decide ((source.inputHead : ℤ) = 0)) (wordTape B word source.inputHead).2)
            .stay .stay .stay none := by
  simp [TapeBank.instruction, bank, inspecting, configuration, decisionData, generatorData]
  rfl

def committing (word : Word α) (offset : ℕ) (source : BankConfiguration Unit Q S k)
    (next : Q) (write : S) (work input : Move) :
    BankConfiguration α (Control B fallback) (Cell S α) (k + 1) :=
  {configuration B fallback word offset source with
    state := .commit (B.select source.state) next write work
    head := Fin.lastCases (input.onInput word.length source.inputHead : ℤ) source.head}

end
end ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration
