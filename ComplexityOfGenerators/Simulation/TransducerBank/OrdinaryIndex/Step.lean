import ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

@[simp] theorem read_indexTape (length position : ℕ) :
    readIndex (indexTape B length position) = (if position < length then some () else none) := by
  by_cases inside : position < length <;> simp [indexTape, readIndex, inside]

theorem indexMove_position (length position : ℕ) (inside : position ≤ length) (move : Move) :
    (indexMove move (decide ((position : ℤ) = 0)) (indexTape B length position)).onInt position =
      (move.onInput length position : ℤ) := by
  cases move with
  | left =>
    by_cases zero : position = 0
    · subst position; simp [indexMove, Move.onInput, Move.onInt]
    · simp [indexMove, Move.onInput, zero, Move.onInt]; omega
  | stay => simp [indexMove, Move.onInput, Move.onInt]; omega
  | right =>
    by_cases ended : position < length <;>
      simp [indexMove, read_indexTape, ended, Move.onInput, Move.onInt] <;> omega

theorem fetch_step (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (bounds : B.Bounded (sourceData data) r source) :
    (bank B).Steps data bits (configuration B data source) 1 (inspecting B data source) := by
  apply TapeBank.Steps.go (bank B) data bits _ _
    bounds.input bounds.auxiliary (Nat.zero_le _)
  simp [TapeBank.instruction, bank, configuration, readWork, inspecting]

theorem inspect_instruction (data : InputData I A) (source : BankConfiguration O Q S k) :
    (bank B).instruction data (inspecting B data source) =
      match B.instruction (sourceData data) source with
      | .accept => .accept
      | .reject => .reject
      | .readRandom no yes => .readRandom (.fetch no) (.fetch yes)
      | .step next write work input auxiliary index emit =>
          .step (.commit (B.select source.state) next write work)
            (indexTape B data.input.length source.indexHead)
            (indexMove index (decide ((source.indexHead : ℤ) = 0))
              (indexTape B data.input.length source.indexHead)) input auxiliary .stay emit := by
  simp [TapeBank.instruction, bank, inspecting, configuration, sourceData]
  rfl

end
end ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex
