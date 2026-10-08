import ComplexityOfGenerators.Proofs.BinarySampling
import ComplexityOfGenerators.Simulation.BinaryInput

/-! Primitive operational lemmas for the actual random-input transition table.
The invariant tracks the written stack cells and the consumed random prefix. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

def BinaryPrepared (phase : BinaryInputControl states) (written : List RecursiveAlphabet)
    (consumed : ℕ) (c : Configuration (binaryInputMachine program control alphabet)) : Prop :=
  c.state = binaryInputControl phase ∧ c.workHead = (written.length : ℤ) ∧
    c.randomHead = consumed ∧ c.work = bootMemory alphabet written written.length ∧ c.output = []

theorem binary_input_write (data : InputData Unit Bool) (bits : BitString)
    (phase next : BinaryInputControl states) (written : List RecursiveAlphabet)
    (consumed : ℕ) (symbol : RecursiveAlphabet)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet phase written consumed c)
    (table : binaryInputInstruction program control alphabet phase (c.work c.workHead) =
      .step (binaryInputControl next) (some (bootEncode alphabet symbol)) .right .stay .stay .stay none) :
    ∃ d, BinaryPrepared program control alphabet next (written ++ [symbol]) consumed d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c 1 =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  obtain ⟨state, head, random, memory, output⟩ := prepared
  let d := M.stepConfiguration data c (binaryInputControl next)
    (some (bootEncode alphabet symbol)) .right .stay .stay .stay none
  have instruction : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .step (binaryInputControl next) (some (bootEncode alphabet symbol)) .right .stay .stay .stay none := by
    simpa [M, binaryInputMachine, state] using table
  have live := M.observe_step data bits c _ _ _ _ _ _ _ instruction
  have step := M.next_step data bits c _ _ _ _ _ _ _ instruction
  refine ⟨d, ⟨rfl, ?_, random, ?_, output⟩, ?_⟩
  · simp [d, Machine.stepConfiguration, Move.onInt, head]
  · change Function.update c.work c.workHead (some (bootEncode alphabet symbol)) = _
    rw [memory, head]
    exact bootMemory_write_append alphabet written symbol
  · exact M.runFrom_shift data bits c d live step 0

theorem binary_input_random (data : InputData Unit Bool) (bits : BitString)
    (phase onFalse onTrue : BinaryInputControl states) (written : List RecursiveAlphabet)
    (consumed : ℕ) (bit : Bool)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet phase written consumed c)
    (available : bits[consumed]? = some bit)
    (table : binaryInputInstruction program control alphabet phase (c.work c.workHead) =
      .readRandom (binaryInputControl onFalse) (binaryInputControl onTrue)) :
    ∃ d, BinaryPrepared program control alphabet (if bit then onTrue else onFalse) written (consumed + 1) d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c 1 =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  obtain ⟨state, head, random, memory, output⟩ := prepared
  let d : Configuration M := { c with
    state := if bit then binaryInputControl onTrue else binaryInputControl onFalse
    randomHead := consumed + 1 }
  have instruction : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .readRandom (binaryInputControl onFalse) (binaryInputControl onTrue) := by
    simpa [M, binaryInputMachine, state] using table
  have bound : consumed < bits.length := by
    by_contra outside
    have missing : bits[consumed]? = none := List.getElem?_eq_none (by omega)
    rw [missing] at available
    contradiction
  have live : M.observe data bits c = .running c := by
    simp [Machine.observe, instruction, random, bound]
  have step : M.next data bits c = .running d := by
    simp [Machine.next, instruction, random, available, d]
  refine ⟨d, ⟨?_, head, rfl, memory, output⟩, ?_⟩
  · cases bit <;> rfl
  · exact M.runFrom_shift data bits c d live step 0

theorem binary_input_exhausts (data : InputData Unit Bool) (bits : BitString)
    (phase onFalse onTrue : BinaryInputControl states) (written : List RecursiveAlphabet)
    (consumed : ℕ) (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet phase written consumed c)
    (missing : bits.length ≤ consumed)
    (table : binaryInputInstruction program control alphabet phase (c.work c.workHead) =
      .readRandom (binaryInputControl onFalse) (binaryInputControl onTrue)) :
    (binaryInputMachine program control alphabet).observe data bits c = .halted .exhausted := by
  obtain ⟨state, head, random, memory, output⟩ := prepared
  have instruction : (binaryInputMachine program control alphabet).transition c.state
      data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .readRandom (binaryInputControl onFalse) (binaryInputControl onTrue) := by
    simpa [binaryInputMachine, state] using table
  simp [Machine.observe, instruction, random, show ¬ consumed < bits.length by omega]

end

end ComplexityOfGenerators
