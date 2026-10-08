import ComplexityOfGenerators.Proofs.BinaryInputCorrectness
import ComplexityOfGenerators.Simulation.RoutineExecution
import ComplexityOfGenerators.Simulation.PostOutput

/-! Initialization inside a composed native machine. The proof stops at the
rewind marker before entering the Post program, so even a program that halts
immediately transfers its actual work tape to the output continuation. -/

namespace ComplexityOfGenerators

open Simulation Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {Q : Type} [Inhabited Q] {states symbols : ℕ}
variable (program : TM0.Machine RecursiveAlphabet Q) (control : Q ≃ Fin states)
variable (alphabet : RecursiveAlphabet ≃ Fin symbols)

theorem binary_input_rewind_to_marker (data : InputData Unit Bool) (bits : BitString)
    (word : List RecursiveAlphabet) (r : ℕ) (bound : r ≤ word.length + 1)
    (c : Configuration (binaryInputMachine program control alphabet))
    (prepared : BinaryRewinding program control alphabet word r c) :
    ∃ d, BinaryRewinding program control alphabet word 0 d ∧
      (binaryInputMachine program control alphabet).runFrom data bits c r = .running d := by
  let M := binaryInputMachine program control alphabet
  induction r generalizing c with
  | zero =>
      refine ⟨c, prepared, ?_⟩
      obtain ⟨state, head, memory, output⟩ := prepared
      have marker : c.work c.workHead = some (Fin.last symbols) := by simp [memory, head, bootMemory]
      simp [Machine.runFrom, Machine.observe, binaryInputMachine, state,
        binaryInputInstruction, marker]
  | succ r ih =>
      obtain ⟨state, head, memory, output⟩ := prepared
      have position : ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) := by omega
      have unmarked : c.work c.workHead ≠ some (Fin.last symbols) := by
        rw [memory, head, position]
        by_cases inside : r < word.length
        · exact bootMemory_not_marker alphabet word r inside
        · have atEnd : r = word.length := by omega
          subst r
          have notMarker : (word.length : ℤ) ≠ -1 := by omega
          simp [bootMemory, notMarker]
      let next := M.stepConfiguration data c (binaryInputControl .rewind) none .left .stay .stay .stay none
      have table : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
          (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
          .step (binaryInputControl .rewind) none .left .stay .stay .stay none := by
        simp [M, binaryInputMachine, state, binaryInputInstruction, unmarked]
      have live := M.observe_step data bits c _ _ _ _ _ _ _ table
      have step := M.next_step data bits c _ _ _ _ _ _ _ table
      have nextReady : BinaryRewinding program control alphabet word r next := by
        refine ⟨rfl, ?_, memory, output⟩
        change c.workHead - 1 = (r : ℤ) - 1
        rw [head, position]
      obtain ⟨d, final, execution⟩ := ih (by omega) next nextReady
      exact ⟨d, final, (M.runFrom_shift data bits c next live step r).trans execution⟩

theorem binary_input_bootstrap_marker (data : InputData Unit Bool) (candidate clock : Num)
    (extra : BitString) :
    ∃ t d, BinaryRewinding program control alphabet (recursiveInput [(clock : ℕ), (candidate : ℕ)]) 0 d ∧
      (binaryInputMachine program control alphabet).run data
        (numSeed candidate ++ numSeed clock ++ extra) t = .running d := by
  let M := binaryInputMachine program control alphabet
  let bits := numSeed candidate ++ numSeed clock ++ extra
  let word := recursiveInput [(clock : ℕ), (candidate : ℕ)]
  obtain ⟨initial, initialReady, initialRun⟩ := binary_input_initial program control alphabet data bits
  obtain ⟨pairTime, sampled, sampledReady, pairRun⟩ := binary_input_pair program control alphabet data bits
    candidate clock extra 0 initial initialReady (by simp [bits])
  obtain ⟨rewinding, rewindingReady, skip⟩ := binary_input_skip program control alphabet data bits
    (.finish true) .rewind word ((numSeed candidate).length + (numSeed clock).length)
    sampled (by simpa using sampledReady) rfl
  have rewindReady : BinaryRewinding program control alphabet word (word.length + 1) rewinding := by
    obtain ⟨state, head, random, memory, output⟩ := rewindingReady
    refine ⟨state, ?_, memory, output⟩
    rw [head]
    omega
  obtain ⟨d, final, rewind⟩ := binary_input_rewind_to_marker program control alphabet data bits word
    (word.length + 1) (by omega) rewinding rewindReady
  refine ⟨3 + (pairTime + (1 + (word.length + 1))), d, final, ?_⟩
  rw [← M.runFrom_initial] at initialRun ⊢
  exact (M.runFrom_add data bits M.initialConfiguration initial 3 initialRun
      (pairTime + (1 + (word.length + 1)))).trans
    ((M.runFrom_add data bits initial sampled pairTime pairRun (1 + (word.length + 1))).trans
      ((M.runFrom_add data bits sampled rewinding 1 skip (word.length + 1)).trans rewind))

variable {α : Type} [Fintype α] [Encodable α]

omit [Encodable α] in
/-- A native sampler followed by an arbitrary work-tape routine initializes the
source computation correctly, including when that computation immediately halts. -/
theorem sequence_binary_input_bootstrap
    (routine : Routine Unit Bool α (binaryInputMachine program control alphabet).symbols)
    (data : InputData Unit Bool) (candidate clock : ℕ) (extra : BitString) :
    ∃ t d, PostRelated (binaryInputSimulator program control alphabet)
        (TM0.init (recursiveInput [clock, candidate])) d ∧
      (sequenceMachine (binaryInputMachine program control alphabet) routine).run data
        (binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra) t =
        (sequenceMachine (binaryInputMachine program control alphabet) routine).observe data
          (binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra)
          (sequenceLeftConfiguration (binaryInputMachine program control alphabet) routine d []) := by
  let M := binaryInputMachine program control alphabet
  let combined := sequenceMachine M routine
  let bits := binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra
  let word := recursiveInput [clock, candidate]
  have initialized := binary_input_bootstrap_marker program control alphabet data (candidate : Num) (clock : Num) extra
  norm_cast at initialized
  obtain ⟨t, c, prepared, execution⟩ := initialized
  obtain ⟨state, head, memory, output⟩ := prepared
  have marker : c.work c.workHead = some (Fin.last symbols) := by simp [memory, head, bootMemory]
  let d := M.stepConfiguration data c (binaryInputControl (.run (control default)))
    none .right .stay .stay .stay none
  have table : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some true else none) (c.work c.workHead) =
      .step (binaryInputControl (.run (control default))) none .right .stay .stay .stay none := by
    simp [M, binaryInputMachine, state, binaryInputInstruction, marker]
  have step : M.next data bits c = .running d := M.next_step data bits c _ _ _ _ _ _ _ table
  have lifted := sequence_left_running M routine data bits M.initialConfiguration c [] t
    (by rw [Machine.runFrom_initial]; exact execution)
  have initial : sequenceLeftConfiguration M routine M.initialConfiguration [] = combined.initialConfiguration := rfl
  rw [initial, Machine.runFrom_initial] at lifted
  refine ⟨t + 1, d, ⟨rfl, output, ?_⟩, ?_⟩
  · intro i
    change bootDecode alphabet (c.work ((c.workHead + 1) + i)) = _
    have position : (c.workHead + 1) + i = i := by rw [head]; omega
    rw [position, memory]
    exact bootMemory_input alphabet word i
  · change combined.run data bits (t + 1) = combined.observe data bits (sequenceLeftConfiguration M routine d [])
    change combined.run data bits t = _ at lifted
    simp only [Machine.run, lifted]
    have next := sequence_left_next M routine data bits c d [] step
    change combined.next data bits (sequenceLeftConfiguration M routine c []) = _ at next
    rw [next]

/-- The complete native machine samples its input, executes a terminating Post
program, and emits the word stored in that program's final main stack. -/
theorem binary_post_output_produces (data : InputData Unit Bool)
    (candidate clock : ℕ) (extra : BitString) (word : List α)
    (last : TM0.Cfg RecursiveAlphabet Q)
    (path : TM0.Reaches program (TM0.init (recursiveInput [clock, candidate])) last)
    (halted : program last.q last.Tape.head = none)
    (decoded : ∀ n : ℕ, (last.Tape.nth (n : ℤ)).2 PartrecToTM2.K'.main = (outputCells word)[n]?) :
    (postOutputMachine (α := α) (binaryInputSimulator program control alphabet)).Produces data
      (binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra) word := by
  let sim := binaryInputSimulator program control alphabet
  let routine := postOutputRoutine (α := α) sim
  let combined := postOutputMachine (α := α) sim
  let bits := binaryNumberSeed candidate ++ binaryNumberSeed clock ++ extra
  obtain ⟨t, ready, related, initialized⟩ := sequence_binary_input_bootstrap program control alphabet routine
    data candidate clock extra
  obtain ⟨s, emits⟩ := postOutputMachine_emits_word sim data bits word [] _ last ready related path halted decoded
  refine ⟨t + s, ?_⟩
  change combined.run data bits t = combined.observe data bits
    (sequenceLeftConfiguration sim.machine routine ready []) at initialized
  change combined.run data bits (t + s) = .halted (.accepted word)
  rw [← combined.runFrom_initial] at initialized ⊢
  exact (combined.runFrom_add data bits combined.initialConfiguration
    (sequenceLeftConfiguration sim.machine routine ready []) t initialized s).trans (by simpa using emits)

end

end ComplexityOfGenerators
