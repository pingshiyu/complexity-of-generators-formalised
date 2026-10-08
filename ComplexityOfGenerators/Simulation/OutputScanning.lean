import ComplexityOfGenerators.Simulation.OutputMachine

/-! Operational correctness of the native output routine. The invariant reads
only nonnegative offsets from the current head, which lets the routine operate
on the final main-stack projection without assuming other stacks are erased. -/

namespace ComplexityOfGenerators.Simulation

open Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] [Encodable α] {symbols : ℕ}
variable (read : Option (Fin symbols) → Option PartrecToTM2.Γ')

def OutputReady (phase : OutputControl α) (cells : List PartrecToTM2.Γ')
    (out : List α) (c : Configuration (outputMachine (α := α) symbols read)) : Prop :=
  c.state = outputControl phase ∧ c.output = out ∧
    ∀ k : ℕ, read (c.work (c.workHead + (k : ℤ))) = cells[k]?

theorem output_step_right (data : InputData Unit Bool) (bits : BitString)
    (phase next : OutputControl α) (symbol : PartrecToTM2.Γ')
    (cells : List PartrecToTM2.Γ') (out : List α) (emit : Option α)
    (c : Configuration (outputMachine (α := α) symbols read))
    (ready : OutputReady read phase (symbol :: cells) out c)
    (table : outputInstruction (symbols := symbols) phase (some symbol) =
      .step (outputControl next) none .right .stay .stay .stay emit) :
    ∃ d, OutputReady read next cells (out ++ emit.toList) d ∧
      (outputMachine (α := α) symbols read).runFrom data bits c 1 =
        (outputMachine (α := α) symbols read).observe data bits d := by
  let M := outputMachine (α := α) symbols read
  obtain ⟨state, output, tape⟩ := ready
  have head : read (c.work c.workHead) = some symbol := by simpa using tape 0
  have instruction : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .step (outputControl next) none .right .stay .stay .stay emit := by
    simpa [M, outputMachine, state, head] using table
  let d := M.stepConfiguration data c (outputControl next) none .right .stay .stay .stay emit
  have live := M.observe_step data bits c _ _ _ _ _ _ _ instruction
  have step := M.next_step data bits c _ _ _ _ _ _ _ instruction
  refine ⟨d, ⟨rfl, ?_, ?_⟩, ?_⟩
  · cases emit <;> simp [d, Machine.stepConfiguration, output]
  · intro k
    simpa [d, Machine.stepConfiguration, Move.onInt, Nat.cast_add, add_assoc, add_comm,
      add_left_comm] using tape (k + 1)
  · exact M.runFrom_shift data bits c d live step 0

theorem output_scan_block (data : InputData Unit Bool) (bits : BitString)
    (letter : α) (p : OutputPrefix α) (digits rest : List PartrecToTM2.Γ')
    (whole : p.val ++ digits = outputBlock letter) (out : List α)
    (c : Configuration (outputMachine (α := α) symbols read))
    (ready : OutputReady read (.scan p) (digits ++ rest) out c) :
    ∃ d, OutputReady read
        (.scan ⟨outputBlock letter, prefix_mem_outputPrefixes (List.prefix_refl _)⟩) rest out d ∧
      (outputMachine (α := α) symbols read).runFrom data bits c digits.length =
        (outputMachine (α := α) symbols read).observe data bits d := by
  induction digits generalizing p c with
  | nil =>
      have equal : p = (⟨outputBlock letter, prefix_mem_outputPrefixes (List.prefix_refl _)⟩ : OutputPrefix α) :=
        Subtype.ext (by simpa using whole)
      exact ⟨c, by simpa [equal] using ready, rfl⟩
  | cons bit digits ih =>
      have binary : bit = .bit0 ∨ bit = .bit1 := by
        apply outputBlock_bits letter bit
        rw [← whole]
        simp
      have available : p.val ++ [bit] ∈ outputPrefixes α := by
        apply prefix_mem_outputPrefixes (letter := letter)
        exact ⟨digits, by simpa [List.append_assoc] using whole⟩
      let next : OutputPrefix α := ⟨p.val ++ [bit], available⟩
      have table : outputInstruction (symbols := symbols) (.scan p) (some bit) =
          .step (outputControl (.scan next)) none .right .stay .stay .stay none := by
        rcases binary with rfl | rfl <;>
          simp [outputInstruction, extendOutputPrefix_correct p _ available, next]
      obtain ⟨selected, selectedReady, selection⟩ :=
        output_step_right read data bits (.scan p) (.scan next) bit (digits ++ rest) out none c ready table
      have wholeNext : next.val ++ digits = outputBlock letter := by
        simpa [next, List.append_assoc] using whole
      obtain ⟨d, finalReady, execution⟩ := ih next wholeNext selected (by simpa using selectedReady)
      refine ⟨d, finalReady, ?_⟩
      have composed := (outputMachine (α := α) symbols read).runFrom_add
        data bits c selected 1 selection digits.length
      simpa [Nat.add_comm] using composed.trans execution

end

end ComplexityOfGenerators.Simulation
