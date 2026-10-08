import ComplexityOfGenerators.Simulation.BlockLoading

/-! The loader's leading block, per-letter blocks and trailing block. Each
phase is verified using the one-symbol writing lemma; ordinary input movement
is checked separately from work-tape movement. -/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {I Γ Q : Type} [Fintype I] [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

def leadingPhase (blocks : InputBlocks I Γ) (i : ℕ) : BlockControl blocks states :=
  if h : i < blocks.leading.length then .leading ⟨i, h⟩ else .input

def letterPhase (blocks : InputBlocks I Γ) (letter : I) (i : ℕ) : BlockControl blocks states :=
  if h : i < (blocks.block letter).length then .block letter ⟨i, h⟩ else .advance

def trailingPhase (blocks : InputBlocks I Γ) (i : ℕ) : BlockControl blocks states :=
  if h : i < blocks.trailing.length then .trailing ⟨i, h⟩ else .rewind

omit [Fintype Γ] in
theorem block_leading (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (written : List Γ) (k : ℕ) (bound : k ≤ input.length)
    (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockLoaded program control alphabet blocks blocks.firstPrefix written k target) :
    ∃ ready, BlockLoaded program control alphabet blocks .input (written ++ blocks.leading) k ready ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target blocks.leading.length =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits ready := by
  have table : ∀ i (h : i < blocks.leading.length), ∀ read work,
      blockTransition program control alphabet blocks (leadingPhase blocks i) read work =
        .step (blockControl blocks (leadingPhase blocks (i + 1)))
          (some (bootEncode alphabet (blocks.leading[i]'h))) .right .stay .stay .stay none := by
    intro i h read work
    simp only [leadingPhase, dite_eq_left h, blockTransition]
    rfl
  obtain ⟨ready, loaded, run⟩ := block_chunk program control alphabet blocks input bits blocks.leading
    (leadingPhase blocks) table written k bound 0 blocks.leading.length (by omega) target related
  exact ⟨ready, by simpa [leadingPhase] using loaded, run⟩

omit [Fintype Γ] in
theorem block_letter (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (written : List Γ) (k : ℕ) (letter : I) (available : k < input.length)
    (read : input[k]? = some letter)
    (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockLoaded program control alphabet blocks .input written k target) :
    ∃ ready, BlockLoaded program control alphabet blocks .input (written ++ blocks.block letter) (k + 1) ready ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target
          ((blocks.block letter).length + 2) =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits ready := by
  let M := blockMachine program control alphabet blocks
  have select : blockTransition program control alphabet blocks .input input[k]? (target.work target.workHead) =
      .step (blockControl blocks (letterPhase blocks letter 0)) none .stay .stay .stay .stay none := by
    simp only [blockTransition, read, letterPhase]
    split_ifs <;> rfl
  obtain ⟨selected, selectedRelated, selection⟩ := block_skip program control alphabet blocks input bits
    .input (letterPhase blocks letter 0) written k .stay target related select
  have selectedLoaded : BlockLoaded program control alphabet blocks (letterPhase blocks letter 0) written k selected := by
    simpa [Move.onInput, Nat.min_eq_left available.le] using selectedRelated
  have table : ∀ i (h : i < (blocks.block letter).length), ∀ read work,
      blockTransition program control alphabet blocks (letterPhase blocks letter i) read work =
        .step (blockControl blocks (letterPhase blocks letter (i + 1)))
          (some (bootEncode alphabet ((blocks.block letter)[i]'h))) .right .stay .stay .stay none := by
    intro i h read work
    simp only [letterPhase, dite_eq_left h, blockTransition]
    split_ifs <;> rfl
  obtain ⟨copied, copiedRelated, copy⟩ := block_chunk program control alphabet blocks input bits (blocks.block letter)
    (letterPhase blocks letter) table written k available.le 0 (blocks.block letter).length
    (by omega) selected selectedLoaded
  have copiedLoaded : BlockLoaded program control alphabet blocks .advance (written ++ blocks.block letter) k copied := by
    simpa [letterPhase] using copiedRelated
  obtain ⟨ready, readyRelated, advance⟩ := block_skip program control alphabet blocks input bits
    .advance .input (written ++ blocks.block letter) k .right copied copiedLoaded rfl
  have finalLoaded : BlockLoaded program control alphabet blocks .input (written ++ blocks.block letter) (k + 1) ready := by
    simpa [Move.onInput, Nat.min_eq_left (Nat.succ_le_of_lt available)] using readyRelated
  refine ⟨ready, finalLoaded, ?_⟩
  have first := M.runFrom_add (decisionData input) bits target selected 1 selection ((blocks.block letter).length + 1)
  have second := M.runFrom_add (decisionData input) bits selected copied (blocks.block letter).length copy 1
  have clock : (blocks.block letter).length + 2 = 1 + ((blocks.block letter).length + 1) := by omega
  rw [clock, first, second]
  exact advance

omit [Fintype Γ] in
theorem block_letters (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (remaining : List I) (written : List Γ) (k : ℕ) (bound : k ≤ input.length)
    (rest : input.drop k = remaining)
    (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockLoaded program control alphabet blocks .input written k target) :
    ∃ ready, BlockLoaded program control alphabet blocks .input
        (written ++ remaining.flatMap blocks.block) input.length ready ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target
          ((remaining.flatMap blocks.block).length + 2 * remaining.length) =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits ready := by
  let M := blockMachine program control alphabet blocks
  induction remaining generalizing k written target with
  | nil =>
      have atEnd : k = input.length := by
        have length := congrArg List.length rest
        simp only [List.length_drop, List.length_nil] at length
        omega
      subst k
      exact ⟨target, by simpa using related, rfl⟩
  | cons letter remaining ih =>
      have available : k < input.length := by
        have length := congrArg List.length rest
        simp only [List.length_drop, List.length_cons] at length
        omega
      have read : input[k]? = some letter := by
        have head := congrArg (fun l : List I => l[0]?) rest
        simpa using head
      obtain ⟨copied, copiedRelated, copy⟩ := block_letter program control alphabet blocks input bits
        written k letter available read target related
      have nextRest : input.drop (k + 1) = remaining := by
        have tail := congrArg (List.drop 1) rest
        simpa [List.drop_drop, Nat.add_comm] using tail
      obtain ⟨ready, readyRelated, run⟩ := ih (written ++ blocks.block letter) (k + 1)
        (Nat.succ_le_of_lt available) nextRest copied copiedRelated
      refine ⟨ready, by simpa [List.flatMap_cons, List.append_assoc] using readyRelated, ?_⟩
      have composed := M.runFrom_add (decisionData input) bits target copied
        ((blocks.block letter).length + 2) copy
        ((remaining.flatMap blocks.block).length + 2 * remaining.length)
      have clock : ((letter :: remaining).flatMap blocks.block).length + 2 * (letter :: remaining).length =
          ((blocks.block letter).length + 2) +
            ((remaining.flatMap blocks.block).length + 2 * remaining.length) := by
        simp only [List.flatMap_cons, List.length_append, List.length_cons]
        omega
      rw [clock]
      exact composed.trans run

omit [Fintype Γ] in
theorem block_trailing (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (written : List Γ) (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockLoaded program control alphabet blocks .input written input.length target) :
    ∃ ready, BlockLoaded program control alphabet blocks .rewind (written ++ blocks.trailing) input.length ready ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target
          (blocks.trailing.length + 1) =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits ready := by
  let M := blockMachine program control alphabet blocks
  have select : blockTransition program control alphabet blocks .input input[input.length]?
      (target.work target.workHead) = .step (blockControl blocks (trailingPhase blocks 0))
        none .stay .stay .stay .stay none := by
    simp [blockTransition, trailingPhase, InputBlocks.firstSuffix]
  obtain ⟨selected, selectedRelated, selection⟩ := block_skip program control alphabet blocks input bits
    .input (trailingPhase blocks 0) written input.length .stay target related select
  have selectedLoaded : BlockLoaded program control alphabet blocks (trailingPhase blocks 0) written input.length selected := by
    simpa [Move.onInput] using selectedRelated
  have table : ∀ i (h : i < blocks.trailing.length), ∀ read work,
      blockTransition program control alphabet blocks (trailingPhase blocks i) read work =
        .step (blockControl blocks (trailingPhase blocks (i + 1)))
          (some (bootEncode alphabet (blocks.trailing[i]'h))) .right .stay .stay .stay none := by
    intro i h read work
    simp only [trailingPhase, dite_eq_left h, blockTransition]
    rfl
  obtain ⟨ready, readyRelated, run⟩ := block_chunk program control alphabet blocks input bits blocks.trailing
    (trailingPhase blocks) table written input.length (by rfl) 0 blocks.trailing.length
    (by omega) selected selectedLoaded
  refine ⟨ready, by simpa [trailingPhase] using readyRelated, ?_⟩
  have composed := M.runFrom_add (decisionData input) bits target selected 1 selection blocks.trailing.length
  rw [Nat.add_comm blocks.trailing.length 1]
  exact composed.trans run

end ComplexityOfGenerators.Simulation
