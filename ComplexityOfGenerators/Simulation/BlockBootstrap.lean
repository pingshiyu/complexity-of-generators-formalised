import ComplexityOfGenerators.Simulation.BlockStages

/-! The complete block-loading bootstrap: mark the blank tape, write the
encoded input, rewind, and enter the verified Post simulation. -/

namespace ComplexityOfGenerators.Simulation

open Turing

set_option backward.isDefEq.respectTransparency false

variable {I Γ Q : Type} [Fintype I] [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

omit [Fintype Γ] in
theorem block_initial (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString) :
    ∃ target, BlockLoaded program control alphabet blocks blocks.firstPrefix [] 0 target ∧
      (blockMachine program control alphabet blocks).run (decisionData input) bits 2 =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits target := by
  let M := blockMachine program control alphabet blocks
  let marked := M.stepConfiguration (decisionData input) M.initialConfiguration (blockControl blocks .mark)
    none .left .stay .stay .stay none
  let target := M.stepConfiguration (decisionData input) marked (blockControl blocks blocks.firstPrefix)
    (some (Fin.last symbols)) .right .stay .stay .stay none
  have first : M.transition M.initialConfiguration.state input[M.initialConfiguration.inputHead]?
      (decisionData input).auxiliary[M.initialConfiguration.auxiliaryHead]?
      (if M.initialConfiguration.indexHead < (decisionData input).index then some true else none)
      (M.initialConfiguration.work M.initialConfiguration.workHead) =
      .step (blockControl blocks .mark) none .left .stay .stay .stay none := by
    simp [M, blockMachine, Machine.initialConfiguration, blockTransition]
  have second : M.transition marked.state input[marked.inputHead]?
      (decisionData input).auxiliary[marked.auxiliaryHead]?
      (if marked.indexHead < (decisionData input).index then some true else none)
      (marked.work marked.workHead) =
      .step (blockControl blocks blocks.firstPrefix) (some (Fin.last symbols)) .right .stay .stay .stay none := by
    simp [M, marked, Machine.stepConfiguration, blockMachine, blockTransition]
  have startObservation := M.observe_step (decisionData input) bits M.initialConfiguration _ _ _ _ _ _ _ first
  have startStep := M.next_step (decisionData input) bits M.initialConfiguration _ _ _ _ _ _ _ first
  have markerObservation := M.observe_step (decisionData input) bits marked _ _ _ _ _ _ _ second
  have markerStep := M.next_step (decisionData input) bits marked _ _ _ _ _ _ _ second
  refine ⟨target, ⟨rfl, ?_, ?_, ?_, rfl⟩, ?_⟩
  · simp [target, marked, Machine.stepConfiguration, Machine.initialConfiguration, Move.onInt]
  · simp [target, marked, Machine.stepConfiguration, Machine.initialConfiguration, Move.onInput, decisionData]
  · funext i
    have outside : ¬ (0 ≤ i ∧ i < (0 : ℤ)) := by omega
    simp [target, marked, Machine.stepConfiguration, Machine.initialConfiguration,
      Move.onInt, bootMemory, outside, Function.update_apply]
  · rw [← M.runFrom_initial]
    exact (M.runFrom_shift (decisionData input) bits M.initialConfiguration marked startObservation startStep 1).trans
      (M.runFrom_shift (decisionData input) bits marked target markerObservation markerStep 0)

def BlockRewinding (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (word : List Γ) (r : ℕ)
    (target : Configuration (blockMachine program control alphabet blocks)) : Prop :=
  target.state = blockControl blocks .rewind ∧ target.workHead = (r : ℤ) - 1 ∧
    target.work = bootMemory alphabet word word.length ∧ target.output = []

omit [Fintype Γ] in
theorem block_rewind (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (word : List Γ) (r : ℕ) (bound : r ≤ word.length + 1)
    (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockRewinding program control alphabet blocks word r target) :
    ∃ ready, PostRelated (blockSimulator program control alphabet blocks) (TM0.init word) ready ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target (r + 1) =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits ready := by
  let M := blockMachine program control alphabet blocks
  induction r generalizing target with
  | zero =>
      obtain ⟨state, head, memory, output⟩ := related
      have marker : target.work target.workHead = some (Fin.last symbols) := by
        simp [memory, head, bootMemory]
      let ready := M.stepConfiguration (decisionData input) target
        (blockControl blocks (.run (control default))) none .right .stay .stay .stay none
      have transition : M.transition target.state input[target.inputHead]?
          (decisionData input).auxiliary[target.auxiliaryHead]?
          (if target.indexHead < (decisionData input).index then some true else none)
          (target.work target.workHead) =
          .step (blockControl blocks (.run (control default))) none .right .stay .stay .stay none := by
        simp [M, blockMachine, state, blockTransition, marker]
      have observation := M.observe_step (decisionData input) bits target _ _ _ _ _ _ _ transition
      have step := M.next_step (decisionData input) bits target _ _ _ _ _ _ _ transition
      refine ⟨ready, ⟨rfl, output, ?_⟩, M.runFrom_shift _ bits target ready observation step 0⟩
      intro i
      change bootDecode alphabet (target.work ((target.workHead + 1) + i)) = _
      have position : (target.workHead + 1) + i = i := by rw [head]; omega
      rw [position, memory]
      exact bootMemory_input alphabet word i
  | succ r ih =>
      obtain ⟨state, head, memory, output⟩ := related
      have position : ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) := by omega
      have unmarked : target.work target.workHead ≠ some (Fin.last symbols) := by
        rw [memory, head, position]
        by_cases inside : r < word.length
        · exact bootMemory_not_marker alphabet word r inside
        · have atEnd : r = word.length := by omega
          subst r
          have notMarker : (word.length : ℤ) ≠ -1 := by omega
          simp [bootMemory, notMarker]
      let nextTarget := M.stepConfiguration (decisionData input) target (blockControl blocks .rewind)
        none .left .stay .stay .stay none
      have transition : M.transition target.state input[target.inputHead]?
          (decisionData input).auxiliary[target.auxiliaryHead]?
          (if target.indexHead < (decisionData input).index then some true else none)
          (target.work target.workHead) =
          .step (blockControl blocks .rewind) none .left .stay .stay .stay none := by
        simp only [M, blockMachine, state, Equiv.symm_apply_apply, blockTransition, ite_eq_right unmarked]
      have observation := M.observe_step (decisionData input) bits target _ _ _ _ _ _ _ transition
      have step := M.next_step (decisionData input) bits target _ _ _ _ _ _ _ transition
      have nextRelated : BlockRewinding program control alphabet blocks word r nextTarget := by
        refine ⟨rfl, ?_, memory, output⟩
        change target.workHead - 1 = (r : ℤ) - 1
        rw [head, position]
      obtain ⟨ready, readyRelated, run⟩ := ih (by omega) nextTarget nextRelated
      exact ⟨ready, readyRelated,
        (M.runFrom_shift (decisionData input) bits target nextTarget observation step (r + 1)).trans run⟩

omit [Fintype Γ] in
/-- Exact runtime for loading and rewinding a block encoding. In particular,
the input starts on a blank work tape and is read in its original alphabet. -/
theorem block_bootstrap (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString) :
    ∃ ready, PostRelated (blockSimulator program control alphabet blocks) (TM0.init (blocks.word input)) ready ∧
      (blockMachine program control alphabet blocks).run (decisionData input) bits
          (2 * (blocks.word input).length + 2 * input.length + 5) =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits ready := by
  let M := blockMachine program control alphabet blocks
  obtain ⟨initial, initialRelated, initialized⟩ := block_initial program control alphabet blocks input bits
  obtain ⟨leading, leadingRelated, leadingRun⟩ := block_leading program control alphabet blocks input bits
    [] 0 (by omega) initial initialRelated
  have leadingLoaded : BlockLoaded program control alphabet blocks .input blocks.leading 0 leading := by
    simpa using leadingRelated
  obtain ⟨letters, lettersRelated, lettersRun⟩ := block_letters program control alphabet blocks input bits
    input blocks.leading 0 (by omega) (by simp) leading leadingLoaded
  obtain ⟨trailing, trailingRelated, trailingRun⟩ := block_trailing program control alphabet blocks input bits
    (blocks.leading ++ input.flatMap blocks.block) letters lettersRelated
  have rewinding : BlockRewinding program control alphabet blocks (blocks.word input)
      ((blocks.word input).length + 1) trailing := by
    obtain ⟨state, head, _, memory, output⟩ := trailingRelated
    refine ⟨state, ?_, ?_, output⟩
    · simpa [InputBlocks.word, List.append_assoc] using head
    · simpa [InputBlocks.word, List.append_assoc] using memory
  obtain ⟨ready, readyRelated, rewindRun⟩ := block_rewind program control alphabet blocks input bits
    (blocks.word input) ((blocks.word input).length + 1) (by rfl) trailing rewinding
  have initRun : M.runFrom (decisionData input) bits M.initialConfiguration 2 = M.observe (decisionData input) bits initial := by
    simpa using initialized
  have runLeading := M.runFrom_add (decisionData input) bits M.initialConfiguration initial 2 initRun
    (blocks.leading.length + ((input.flatMap blocks.block).length + 2 * input.length +
      (blocks.trailing.length + 1 + ((blocks.word input).length + 1 + 1))))
  have runLetters := M.runFrom_add (decisionData input) bits initial leading blocks.leading.length leadingRun
    ((input.flatMap blocks.block).length + 2 * input.length +
      (blocks.trailing.length + 1 + ((blocks.word input).length + 1 + 1)))
  have runTrailing := M.runFrom_add (decisionData input) bits leading letters
    ((input.flatMap blocks.block).length + 2 * input.length) lettersRun
    (blocks.trailing.length + 1 + ((blocks.word input).length + 1 + 1))
  have runRewind := M.runFrom_add (decisionData input) bits letters trailing (blocks.trailing.length + 1) trailingRun
    ((blocks.word input).length + 1 + 1)
  refine ⟨ready, readyRelated, ?_⟩
  have length : (blocks.word input).length = blocks.leading.length +
      (input.flatMap blocks.block).length + blocks.trailing.length := by
    simp only [InputBlocks.word, List.length_append]
  have clock : 2 * (blocks.word input).length + 2 * input.length + 5 =
      2 + (blocks.leading.length + ((input.flatMap blocks.block).length + 2 * input.length +
        (blocks.trailing.length + 1 + ((blocks.word input).length + 1 + 1)))) := by omega
  rw [clock, ← M.runFrom_initial]
  rw [runLeading, runLetters, runTrailing, runRewind]
  exact rewindRun

end ComplexityOfGenerators.Simulation
