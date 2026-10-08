import ComplexityOfGenerators.Simulation.BlockLoader

/-! Operational correctness of the concrete block loader. The invariant tracks
the entire tape written so far, the ordinary input position, and the exact
finite-control phase. Work cells not written by the loader stay blank. -/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {I Γ Q : Type} [Fintype I] [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

omit [Fintype I] [Fintype Γ] [Inhabited Q] in
theorem bootMemory_append_before (alphabet : Γ ≃ Fin symbols) (written : List Γ) (symbol : Γ) :
    bootMemory alphabet (written ++ [symbol]) written.length =
      bootMemory alphabet written written.length := by
  funext i
  by_cases marker : i = -1
  · simp [bootMemory, marker]
  · by_cases inside : 0 ≤ i ∧ i < (written.length : ℤ)
    · have bound : i.toNat < written.length := by omega
      have extended : i.toNat < (written ++ [symbol]).length := by simp; omega
      simp only [bootMemory, ite_eq_right marker, ite_eq_left inside]
      rw [List.getD_eq_getElem _ _ extended, List.getD_eq_getElem _ _ bound,
        List.getElem_append_left bound]
    · simp [bootMemory, marker, inside]

omit [Fintype I] [Fintype Γ] [Inhabited Q] in
theorem bootMemory_write_append (alphabet : Γ ≃ Fin symbols) (written : List Γ) (symbol : Γ) :
    Function.update (bootMemory alphabet written written.length) (written.length : ℤ)
      (some (bootEncode alphabet symbol)) =
      bootMemory alphabet (written ++ [symbol]) (written ++ [symbol]).length := by
  have update := bootMemory_update alphabet (written ++ [symbol]) written.length
    (by simp : written.length < (written ++ [symbol]).length)
  rw [bootMemory_append_before] at update
  simpa using update

def BlockLoaded (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (phase : BlockControl blocks states)
    (written : List Γ) (inputHead : ℕ)
    (target : Configuration (blockMachine program control alphabet blocks)) : Prop :=
  target.state = blockControl blocks phase ∧ target.workHead = (written.length : ℤ) ∧
    target.inputHead = inputHead ∧ target.work = bootMemory alphabet written written.length ∧
    target.output = []

omit [Fintype Γ] in
theorem block_write (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (phase nextPhase : BlockControl blocks states) (written : List Γ) (k : ℕ) (symbol : Γ)
    (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockLoaded program control alphabet blocks phase written k target)
    (bound : k ≤ input.length)
    (instruction : blockTransition program control alphabet blocks phase
      input[k]? (target.work target.workHead) = .step (blockControl blocks nextPhase)
        (some (bootEncode alphabet symbol)) .right .stay .stay .stay none) :
    ∃ nextTarget, BlockLoaded program control alphabet blocks nextPhase (written ++ [symbol]) k nextTarget ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target 1 =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits nextTarget := by
  let M := blockMachine program control alphabet blocks
  obtain ⟨state, head, inputHead, memory, output⟩ := related
  let nextTarget := M.stepConfiguration (decisionData input) target (blockControl blocks nextPhase)
    (some (bootEncode alphabet symbol)) .right .stay .stay .stay none
  have transition : M.transition target.state input[target.inputHead]?
      (decisionData input).auxiliary[target.auxiliaryHead]?
      (if target.indexHead < (decisionData input).index then some true else none)
      (target.work target.workHead) = .step (blockControl blocks nextPhase)
        (some (bootEncode alphabet symbol)) .right .stay .stay .stay none := by
    simpa [M, blockMachine, state, inputHead] using instruction
  have observation := M.observe_step (decisionData input) bits target _ _ _ _ _ _ _ transition
  have step := M.next_step (decisionData input) bits target _ _ _ _ _ _ _ transition
  refine ⟨nextTarget, ⟨rfl, ?_, ?_, ?_, output⟩, ?_⟩
  · simp [nextTarget, Machine.stepConfiguration, Move.onInt, head]
  · simp [nextTarget, Machine.stepConfiguration, Move.onInput, decisionData, inputHead, Nat.min_eq_left bound]
  · change Function.update target.work target.workHead (some (bootEncode alphabet symbol)) = _
    rw [memory, head]
    exact bootMemory_write_append alphabet written symbol
  · exact M.runFrom_shift (decisionData input) bits target nextTarget observation step 0

omit [Fintype Γ] in
theorem block_skip (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (phase nextPhase : BlockControl blocks states) (written : List Γ) (k : ℕ) (inputMove : Move)
    (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockLoaded program control alphabet blocks phase written k target)
    (instruction : blockTransition program control alphabet blocks phase input[k]? (target.work target.workHead) =
      .step (blockControl blocks nextPhase) none .stay inputMove .stay .stay none) :
    ∃ nextTarget, BlockLoaded program control alphabet blocks nextPhase written
        (inputMove.onInput input.length k) nextTarget ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target 1 =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits nextTarget := by
  let M := blockMachine program control alphabet blocks
  obtain ⟨state, head, inputHead, memory, output⟩ := related
  let nextTarget := M.stepConfiguration (decisionData input) target (blockControl blocks nextPhase)
    none .stay inputMove .stay .stay none
  have transition : M.transition target.state input[target.inputHead]?
      (decisionData input).auxiliary[target.auxiliaryHead]?
      (if target.indexHead < (decisionData input).index then some true else none)
      (target.work target.workHead) = .step (blockControl blocks nextPhase) none .stay inputMove .stay .stay none := by
    simpa [M, blockMachine, state, inputHead] using instruction
  have observation := M.observe_step (decisionData input) bits target _ _ _ _ _ _ _ transition
  have step := M.next_step (decisionData input) bits target _ _ _ _ _ _ _ transition
  refine ⟨nextTarget, ⟨rfl, head, ?_, memory, output⟩, ?_⟩
  · simp [nextTarget, Machine.stepConfiguration, decisionData, inputHead]
  · exact M.runFrom_shift (decisionData input) bits target nextTarget observation step 0

omit [Fintype Γ] in
/-- A fixed word is written one symbol per transition. The table-equality
hypothesis is checked for each concrete prefix, letter block and suffix below. -/
theorem block_chunk (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (blocks : InputBlocks I Γ) (input : List I) (bits : BitString)
    (word : List Γ) (phase : ℕ → BlockControl blocks states)
    (table : ∀ i (h : i < word.length), ∀ read work,
      blockTransition program control alphabet blocks (phase i) read work =
        .step (blockControl blocks (phase (i + 1))) (some (bootEncode alphabet (word[i]'h)))
          .right .stay .stay .stay none)
    (written : List Γ) (k : ℕ) (bound : k ≤ input.length) (i remaining : ℕ)
    (finish : i + remaining = word.length)
    (target : Configuration (blockMachine program control alphabet blocks))
    (related : BlockLoaded program control alphabet blocks (phase i) written k target) :
    ∃ ready, BlockLoaded program control alphabet blocks (phase word.length)
        (written ++ word.drop i) k ready ∧
      (blockMachine program control alphabet blocks).runFrom (decisionData input) bits target remaining =
        (blockMachine program control alphabet blocks).observe (decisionData input) bits ready := by
  let M := blockMachine program control alphabet blocks
  induction remaining generalizing i written target with
  | zero =>
      have endIndex : i = word.length := by omega
      subst i
      exact ⟨target, by simpa using related, rfl⟩
  | succ remaining ih =>
      have available : i < word.length := by omega
      obtain ⟨nextTarget, nextRelated, step⟩ := block_write program control alphabet blocks input bits
        (phase i) (phase (i + 1)) written k word[i] target related bound
        (table i available _ _)
      obtain ⟨ready, readyRelated, run⟩ := ih (written ++ [word[i]]) (i + 1)
        (by omega) nextTarget nextRelated
      refine ⟨ready, ?_, ?_⟩
      · have suffix : word.drop i = word[i] :: word.drop (i + 1) :=
          (List.getElem_cons_drop available).symm
        have sameWritten : (written ++ [word[i]]) ++ word.drop (i + 1) = written ++ word.drop i := by
          calc
            _ = written ++ (word[i] :: word.drop (i + 1)) := by
              simp only [List.append_assoc, List.singleton_append]
            _ = _ := congrArg (List.append written) suffix.symm
        rw [sameWritten] at readyRelated
        exact readyRelated
      · have composed := M.runFrom_add (decisionData input) bits target nextTarget 1 step remaining
        rw [Nat.add_comm remaining 1]
        exact composed.trans run

end ComplexityOfGenerators.Simulation
