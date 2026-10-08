import ComplexityOfGenerators.Simulation.BlockBootstrap
import ComplexityOfGenerators.Simulation.TapeScan

/-! A loader snapshot immediately before the final transition into its source
program. Unlike an equality of halting observations, this running configuration
retains the actual work tape needed for sequential composition. -/

namespace ComplexityOfGenerators.Simulation

open Turing

set_option backward.isDefEq.respectTransparency false

variable {I Γ Q : Type} [Fintype I] [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

omit [Fintype Γ] in
theorem block_loaded_prefix (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString) :
    ∃ target, BlockLoaded program control alphabet blocks .rewind (blocks.word input) input.length target ∧
      (blockMachine program control alphabet blocks).run (decisionData input) bits
        ((blocks.word input).length + 2 * input.length + 3) =
      (blockMachine program control alphabet blocks).observe (decisionData input) bits target := by
  let M := blockMachine program control alphabet blocks
  obtain ⟨initial, initialRelated, initialized⟩ := block_initial program control alphabet blocks input bits
  obtain ⟨leading, leadingRelated, leadingRun⟩ := block_leading program control alphabet blocks input bits
    [] 0 (by omega) initial initialRelated
  have leadingLoaded : BlockLoaded program control alphabet blocks .input blocks.leading 0 leading := by
    simpa using leadingRelated
  obtain ⟨letters, lettersRelated, lettersRun⟩ := block_letters program control alphabet blocks input bits
    input blocks.leading 0 (by omega) (by simp) leading leadingLoaded
  obtain ⟨target, related, trailingRun⟩ := block_trailing program control alphabet blocks input bits
    (blocks.leading ++ input.flatMap blocks.block) letters lettersRelated
  refine ⟨target, by simpa [InputBlocks.word, List.append_assoc] using related, ?_⟩
  have first : M.runFrom (decisionData input) bits M.initialConfiguration 2 = M.observe (decisionData input) bits initial := by
    simpa using initialized
  have clock : (blocks.word input).length + 2 * input.length + 3 =
      2 + (blocks.leading.length + ((input.flatMap blocks.block).length + 2 * input.length + (blocks.trailing.length + 1))) := by
    simp only [InputBlocks.word, List.length_append]
    omega
  rw [clock, ← M.runFrom_initial,
    M.runFrom_add (decisionData input) bits M.initialConfiguration initial 2 first,
    M.runFrom_add (decisionData input) bits initial leading blocks.leading.length leadingRun,
    M.runFrom_add (decisionData input) bits leading letters ((input.flatMap blocks.block).length + 2 * input.length) lettersRun]
  exact trailingRun

omit [Fintype Γ] in
/-- The actual running configuration at the left marker, with the loaded tape
still intact. This is the compositional entry point for a subsequent routine. -/
theorem block_at_marker (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString) :
    ∃ target,
      target.state = blockControl blocks .rewind ∧ target.workHead = -1 ∧
      target.work = bootMemory alphabet (blocks.word input) (blocks.word input).length ∧ target.output = [] ∧
      (blockMachine program control alphabet blocks).run (decisionData input) bits
        (2 * (blocks.word input).length + 2 * input.length + 4) = .running target := by
  let M := blockMachine program control alphabet blocks
  let word := blocks.word input
  obtain ⟨loaded, ⟨state, head, _, memory, output⟩, loadedRun⟩ :=
    block_loaded_prefix program control alphabet blocks input bits
  obtain ⟨target, targetState, targetHead, targetMemory, _, targetOutput, rewindRun⟩ :=
    tapeScan M (decisionData input) bits loaded (blockControl blocks .rewind)
      (fun k => (word.length : ℤ) - k) (fun _ => .left) (word.length + 1) state
      (by simpa [word] using head)
      (fun k _ => by simp only [Move.onInt]; omega)
      (fun k hk read auxiliary index => by
        have nonnegative : 0 ≤ (word.length : ℤ) - k := by omega
        have upper : (word.length : ℤ) - k ≤ word.length := by omega
        have unmarked : loaded.work ((word.length : ℤ) - k) ≠ some (Fin.last symbols) := by
          rw [memory]
          let i := ((word.length : ℤ) - k).toNat
          have cast : (i : ℤ) = (word.length : ℤ) - k := by dsimp [i]; omega
          rw [← cast]
          by_cases inside : i < word.length
          · exact bootMemory_not_marker alphabet word i inside
          · have atEnd : i = word.length := by omega
            rw [atEnd]
            simp [bootMemory, word]
        simp [M, blockMachine, blockTransition, unmarked])
  have targetAtMarker : target.workHead = -1 := by rw [targetHead]; omega
  have targetTape : target.work = bootMemory alphabet word word.length := targetMemory.trans memory
  have readMarker : target.work target.workHead = some (Fin.last symbols) := by
    simp [targetTape, targetAtMarker, bootMemory]
  have observation : M.observe (decisionData input) bits target = .running target := by
    simp [M, Machine.observe, blockMachine, blockTransition, targetState, readMarker]
  refine ⟨target, targetState, targetAtMarker, targetTape, targetOutput.trans output, ?_⟩
  have clock : 2 * (blocks.word input).length + 2 * input.length + 4 =
      ((blocks.word input).length + 2 * input.length + 3) + (word.length + 1) := by dsimp [word]; omega
  rw [clock, ← M.runFrom_initial,
    M.runFrom_add (decisionData input) bits M.initialConfiguration loaded _ (by simpa using loadedRun)]
  rw [rewindRun, observation]

end ComplexityOfGenerators.Simulation
