import ComplexityOfGenerators.Simulation.OutputScanning

/-! The native output routine emits precisely the computed word and terminates.
Zero-valued letter codes are represented by empty bit blocks between delimiters;
the initial state distinguishes them from an empty word. -/

namespace ComplexityOfGenerators.Simulation

open Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] [Encodable α] {symbols : ℕ}
variable (read : Option (Fin symbols) → Option PartrecToTM2.Γ')

theorem output_finish (data : InputData Unit Bool) (bits : BitString)
    (letter : α) (out : List α)
    (c : Configuration (outputMachine (α := α) symbols read))
    (ready : OutputReady read
      (.scan ⟨outputBlock letter, prefix_mem_outputPrefixes (List.prefix_refl _)⟩) [] out c) :
    (outputMachine (α := α) symbols read).runFrom data bits c 1 =
      .halted (.accepted (out ++ [letter])) := by
  let M := outputMachine (α := α) symbols read
  obtain ⟨state, output, tape⟩ := ready
  have head : read (c.work c.workHead) = none := by simpa using tape 0
  have instruction : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) =
      .step (outputControl .finish) none .stay .stay .stay .stay (some letter) := by
    simp [M, outputMachine, state, head, outputInstruction, decodeOutputPrefix_correct]
  let d := M.stepConfiguration data c (outputControl .finish) none .stay .stay .stay .stay (some letter)
  have live := M.observe_step data bits c _ _ _ _ _ _ _ instruction
  have step := M.next_step data bits c _ _ _ _ _ _ _ instruction
  rw [M.runFrom_shift data bits c d live step 0]
  simp [M, Machine.runFrom, Machine.observe, outputMachine, d,
    Machine.stepConfiguration, outputInstruction, output]

theorem output_letters (data : InputData Unit Bool) (bits : BitString)
    (letter : α) (word out : List α)
    (c : Configuration (outputMachine (α := α) symbols read))
    (ready : OutputReady read (.scan emptyOutputPrefix)
      (outputBlock letter ++ outputCells word) out c) :
    (outputMachine (α := α) symbols read).runFrom data bits c
      ((outputBlock letter).length + (outputCells word).length + 1) =
        .halted (.accepted (out ++ letter :: word)) := by
  induction word generalizing letter out c with
  | nil =>
      obtain ⟨scanned, scannedReady, scan⟩ := output_scan_block read data bits letter emptyOutputPrefix
        (outputBlock letter) [] rfl out c (by simpa [outputCells] using ready)
      have finish := output_finish read data bits letter out scanned scannedReady
      have composed := (outputMachine (α := α) symbols read).runFrom_add
        data bits c scanned (outputBlock letter).length scan 1
      simpa [outputCells] using composed.trans finish
  | cons next word ih =>
      obtain ⟨scanned, scannedReady, scan⟩ := output_scan_block read data bits letter emptyOutputPrefix
        (outputBlock letter) (outputCells (next :: word)) rfl out c ready
      have table : outputInstruction (symbols := symbols)
          (.scan ⟨outputBlock letter, prefix_mem_outputPrefixes (List.prefix_refl _)⟩) (some .cons) =
          .step (outputControl (.scan emptyOutputPrefix)) none .right .stay .stay .stay (some letter) := by
        simp [outputInstruction, decodeOutputPrefix_correct]
      obtain ⟨selected, selectedReady, selection⟩ := output_step_right read data bits
        (.scan ⟨outputBlock letter, prefix_mem_outputPrefixes (List.prefix_refl _)⟩)
        (.scan emptyOutputPrefix) .cons (outputBlock next ++ outputCells word) out (some letter)
        scanned (by simpa [outputCells] using scannedReady) table
      have rest := ih next (out ++ [letter]) selected (by simpa using selectedReady)
      have first := (outputMachine (α := α) symbols read).runFrom_add
        data bits c scanned (outputBlock letter).length scan
        (1 + ((outputBlock next).length + (outputCells word).length + 1))
      have second := (outputMachine (α := α) symbols read).runFrom_add
        data bits scanned selected 1 selection
        ((outputBlock next).length + (outputCells word).length + 1)
      simpa [outputCells, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm,
        List.append_assoc] using
        first.trans (second.trans rest)

/-- A complete operational specification, from a prepared work tape in the
original machine model. The caller supplies the compiled main-stack projection. -/
theorem outputMachine_emits_word (data : InputData Unit Bool) (bits : BitString)
    (word out : List α) (c : Configuration (outputMachine (α := α) symbols read))
    (ready : OutputReady read .start (outputCells word) out c) :
    (outputMachine (α := α) symbols read).runFrom data bits c ((outputCells word).length + 1) =
      .halted (.accepted (out ++ word)) := by
  cases word with
  | nil =>
      obtain ⟨state, output, tape⟩ := ready
      have head : read (c.work c.workHead) = none := by simpa [outputCells] using tape 0
      have halted : (outputMachine (α := α) symbols read).observe data bits c =
          .halted (.accepted out) := by
        simp [Machine.observe, outputMachine, state, head, outputInstruction, output]
      simpa [outputCells] using (outputMachine (α := α) symbols read).runFrom_halted data bits c _ halted 1
  | cons letter word =>
      have table : outputInstruction (symbols := symbols) (OutputControl.start : OutputControl α) (some .cons) =
          .step (outputControl (.scan emptyOutputPrefix)) none .right .stay .stay .stay none := rfl
      obtain ⟨selected, selectedReady, selection⟩ := output_step_right read data bits .start
        (.scan emptyOutputPrefix) .cons (outputBlock letter ++ outputCells word) out none c
        (by simpa [outputCells] using ready) table
      have letters := output_letters read data bits letter word out selected (by simpa using selectedReady)
      have composed := (outputMachine (α := α) symbols read).runFrom_add
        data bits c selected 1 selection ((outputBlock letter).length + (outputCells word).length + 1)
      simpa [outputCells, List.length_append, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        composed.trans letters

end

end ComplexityOfGenerators.Simulation
