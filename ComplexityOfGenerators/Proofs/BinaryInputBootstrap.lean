import ComplexityOfGenerators.Proofs.BinaryInputPair

/-! The binary sampler starts with an initially blank native work tape. This
bootstrap marks its left boundary and writes the main-stack bottom delimiter. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

theorem binary_input_initial (data : InputData Unit Bool) (bits : BitString) :
    ∃ d, BinaryPrepared program control alphabet (.select false) [stackBottom .cons] 0 d ∧
      (binaryInputMachine program control alphabet).run data bits 3 =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  let marked := M.stepConfiguration data M.initialConfiguration (binaryInputControl .mark)
    none .left .stay .stay .stay none
  let bottom := M.stepConfiguration data marked (binaryInputControl .bottom)
    (some (Fin.last symbols)) .right .stay .stay .stay none
  have first : M.transition M.initialConfiguration.state data.input[M.initialConfiguration.inputHead]?
      data.auxiliary[M.initialConfiguration.auxiliaryHead]?
      (if M.initialConfiguration.indexHead < data.index then some true else none)
      (M.initialConfiguration.work M.initialConfiguration.workHead) =
      .step (binaryInputControl .mark) none .left .stay .stay .stay none := by
    simp [M, binaryInputMachine, Machine.initialConfiguration, binaryInputInstruction]
  have second : M.transition marked.state data.input[marked.inputHead]? data.auxiliary[marked.auxiliaryHead]?
      (if marked.indexHead < data.index then some true else none) (marked.work marked.workHead) =
      .step (binaryInputControl .bottom) (some (Fin.last symbols)) .right .stay .stay .stay none := by
    simp [M, marked, Machine.stepConfiguration, binaryInputMachine, binaryInputInstruction]
  have bottomReady : BinaryPrepared program control alphabet .bottom [] 0 bottom := by
    refine ⟨rfl, ?_, rfl, ?_, rfl⟩
    · simp [bottom, marked, Machine.stepConfiguration, Machine.initialConfiguration, Move.onInt]
    · funext i
      have outside : ¬ (0 ≤ i ∧ i < (0 : ℤ)) := by omega
      simp [bottom, marked, Machine.stepConfiguration, Machine.initialConfiguration,
        Move.onInt, bootMemory, outside, Function.update_apply]
  have firstLive := M.observe_step data bits M.initialConfiguration _ _ _ _ _ _ _ first
  have firstStep := M.next_step data bits M.initialConfiguration _ _ _ _ _ _ _ first
  have secondLive := M.observe_step data bits marked _ _ _ _ _ _ _ second
  have secondStep := M.next_step data bits marked _ _ _ _ _ _ _ second
  obtain ⟨d, prepared, written⟩ := binary_input_write program control alphabet data bits
    .bottom (.select false) [] 0 (stackBottom .cons) bottom bottomReady rfl
  refine ⟨d, prepared, ?_⟩
  rw [← M.runFrom_initial]
  exact (M.runFrom_shift data bits M.initialConfiguration marked firstLive firstStep 2).trans
    ((M.runFrom_shift data bits marked bottom secondLive secondStep 1).trans written)

theorem binary_input_skip (data : InputData Unit Bool) (bits : BitString)
    (phase next : BinaryInputControl states) (written : List RecursiveAlphabet) (consumed : ℕ)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryPrepared program control alphabet phase written consumed c)
    (table : binaryInputInstruction program control alphabet phase (c.work c.workHead) =
      .step (binaryInputControl next) none .stay .stay .stay .stay none) :
    ∃ d, BinaryPrepared program control alphabet next written consumed d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c 1 =
        (binaryInputMachine program control alphabet).observe data bits d := by
  let M := binaryInputMachine program control alphabet
  obtain ⟨state, head, random, memory, output⟩ := prepared
  let d := M.stepConfiguration data c (binaryInputControl next) none .stay .stay .stay .stay none
  have instruction : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .step (binaryInputControl next) none .stay .stay .stay .stay none := by
    simpa [M, binaryInputMachine, state] using table
  have live := M.observe_step data bits c _ _ _ _ _ _ _ instruction
  have step := M.next_step data bits c _ _ _ _ _ _ _ instruction
  exact ⟨d, ⟨rfl, head, random, memory, output⟩, M.runFrom_shift data bits c d live step 0⟩

end

end ComplexityOfGenerators
