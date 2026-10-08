import ComplexityOfGenerators.Simulation.PostCore
import Mathlib.Data.List.GetD
import Mathlib.Tactic.IntervalCases

/-!
# Loading inputs and running Post machines

The native work tape starts blank. Four bootstrap states place a marker at cell
`-1`, copy the ordinary input, and rewind to cell `0`. The marker is outside the
source alphabet and decodes as a source blank. Once the bootstrap finishes, the
verified Post simulator executes the source program on its genuine input.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

def bootState (i : Fin 4) : Fin (states + 4) :=
  ⟨i.val, by have bound := i.isLt; omega⟩

def bootControl (control : Q ≃ Fin states) (q : Q) : Fin (states + 4) :=
  (control q).addNat 4

def bootEncode (alphabet : Γ ≃ Fin symbols) (symbol : Γ) : Fin (symbols + 1) :=
  (alphabet symbol).castSucc

def bootDecode (alphabet : Γ ≃ Fin symbols) : Option (Fin (symbols + 1)) → Γ
  | none => default
  | some symbol => if h : symbol.val < symbols then alphabet.symm ⟨symbol.val, h⟩ else default

omit [Fintype Γ] in
@[simp] theorem bootDecode_encode (alphabet : Γ ≃ Fin symbols) (symbol : Γ) :
    bootDecode alphabet (some (bootEncode alphabet symbol)) = symbol := by
  simp [bootDecode, bootEncode]

omit [Fintype Γ] in
@[simp] theorem bootDecode_marker (alphabet : Γ ≃ Fin symbols) :
    bootDecode alphabet (some (Fin.last symbols)) = default := by simp [bootDecode]

def bootTransition (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (q : Fin (states + 4))
    (input : Option Γ) (work : Option (Fin (symbols + 1))) :
    Instruction Unit (states + 4) (symbols + 1) :=
  if phase : q.val < 4 then
    match q.val with
    | 0 => .step (bootState 1) none .left .stay .stay .stay none
    | 1 => .step (bootState 2) (some (Fin.last symbols)) .right .stay .stay .stay none
    | 2 => match input with
      | some symbol => .step (bootState 2) (some (bootEncode alphabet symbol))
          .right .right .stay .stay none
      | none => .step (bootState 3) none .left .stay .stay .stay none
    | _ => if work = some (Fin.last symbols) then
        .step (bootControl control default) none .right .stay .stay .stay none
      else .step (bootState 3) none .left .stay .stay .stay none
  else
    postInstruction (bootControl control) (bootEncode alphabet)
      (program (control.symm (q.subNat 4 (by omega))) (bootDecode alphabet work))

def postMachine (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) : Machine Γ Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := states + 4
  symbols := symbols + 1
  initial := bootState 0
  transition := fun q input _ _ work => bootTransition program control alphabet q input work

def postMachineSimulator (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) : PostSimulator program where
  machine := postMachine program control alphabet
  control := bootControl control
  encode := bootEncode alphabet
  decode := bootDecode alphabet
  writeCorrect := bootDecode_encode alphabet
  transitionCorrect := by
    intro q input auxiliary index work
    simp [postMachine, bootTransition, bootControl]

def bootMemory (alphabet : Γ ≃ Fin symbols) (input : List Γ) (k : ℕ) :
    ℤ → Option (Fin (symbols + 1)) := fun i =>
  if i = -1 then some (Fin.last symbols)
  else if 0 ≤ i ∧ i < (k : ℤ) then some (bootEncode alphabet (input.getD i.toNat default))
  else none

omit [Fintype Γ] in
theorem bootMemory_update (alphabet : Γ ≃ Fin symbols) (input : List Γ) (k : ℕ)
    (available : k < input.length) :
    Function.update (bootMemory alphabet input k) (k : ℤ)
      (some (bootEncode alphabet input[k])) = bootMemory alphabet input (k + 1) := by
  funext i
  by_cases current : i = (k : ℤ)
  · subst i
    have not_marker : (k : ℤ) ≠ -1 := by omega
    have in_range : 0 ≤ (k : ℤ) ∧ (k : ℤ) < ((k + 1 : ℕ) : ℤ) := by omega
    simp [bootMemory, not_marker, in_range, available]
  · have same_range : (0 ≤ i ∧ i < ((k + 1 : ℕ) : ℤ)) ↔ (0 ≤ i ∧ i < (k : ℤ)) := by omega
    simp only [Function.update_of_ne current, bootMemory, same_range]

def CopyRelated (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (k : ℕ)
    (target : Configuration (postMachine program control alphabet)) : Prop :=
  target.state = bootState 2 ∧ target.workHead = (k : ℤ) ∧ target.inputHead = k ∧
    target.work = bootMemory alphabet input k ∧ target.output = []

theorem boot_copy_observe (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString)
    (target : Configuration (postMachine program control alphabet))
    (state : target.state = bootState 2) :
    (postMachine program control alphabet).observe (decisionData input) bits target =
      .running target := by
  cases read : input[target.inputHead]? <;>
    simp [Machine.observe, postMachine, bootTransition, bootState, state, decisionData, read]

theorem boot_copy_step (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) (k : ℕ)
    (target : Configuration (postMachine program control alphabet))
    (related : CopyRelated program control alphabet input k target)
    (available : k < input.length) :
    ∃ nextTarget,
      (postMachine program control alphabet).next (decisionData input) bits target = .running nextTarget ∧
        CopyRelated program control alphabet input (k + 1) nextTarget := by
  obtain ⟨state, head, inputHead, memory, output⟩ := related
  let M := postMachine program control alphabet
  let nextTarget := M.stepConfiguration (decisionData input) target (bootState 2)
    (some (bootEncode alphabet input[k])) .right .right .stay .stay none
  have instruction : M.transition target.state input[target.inputHead]?
      (decisionData input).auxiliary[target.auxiliaryHead]?
      (if target.indexHead < (decisionData input).index then some true else none)
      (target.work target.workHead) = .step (bootState 2)
        (some (bootEncode alphabet input[k])) .right .right .stay .stay none := by
    simp [M, postMachine, bootTransition, state, inputHead, bootState, available]
  refine ⟨nextTarget, M.next_step _ bits target _ _ _ _ _ _ _ instruction, rfl, ?_, ?_, ?_, ?_⟩
  · simp [nextTarget, Machine.stepConfiguration, Move.onInt, head]
  · simp [nextTarget, Machine.stepConfiguration, Move.onInput, decisionData, inputHead,
      Nat.min_eq_left (Nat.succ_le_of_lt available)]
  · change Function.update target.work target.workHead
      (some (bootEncode alphabet input[k])) = bootMemory alphabet input (k + 1)
    rw [memory, head]
    exact bootMemory_update alphabet input k available
  · exact output

theorem boot_copy_initial (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) :
    ∃ target, (postMachine program control alphabet).run (decisionData input) bits 2 = .running target ∧
      CopyRelated program control alphabet input 0 target := by
  let M := postMachine program control alphabet
  let initial := M.initialConfiguration
  let marking := M.stepConfiguration (decisionData input) initial (bootState 1)
    none .left .stay .stay .stay none
  let copying := M.stepConfiguration (decisionData input) marking (bootState 2)
    (some (Fin.last symbols)) .right .stay .stay .stay none
  have initialInstruction : M.transition initial.state input[initial.inputHead]?
      (decisionData input).auxiliary[initial.auxiliaryHead]?
      (if initial.indexHead < (decisionData input).index then some true else none)
      (initial.work initial.workHead) =
        .step (bootState 1) none .left .stay .stay .stay none := by rfl
  have markingInstruction : M.transition marking.state input[marking.inputHead]?
      (decisionData input).auxiliary[marking.auxiliaryHead]?
      (if marking.indexHead < (decisionData input).index then some true else none)
      (marking.work marking.workHead) =
        .step (bootState 2) (some (Fin.last symbols)) .right .stay .stay .stay none := by rfl
  have initialObservation := M.observe_step (decisionData input) bits initial _ _ _ _ _ _ _
    initialInstruction
  have initialNext := M.next_step (decisionData input) bits initial _ _ _ _ _ _ _ initialInstruction
  have markingObservation := M.observe_step (decisionData input) bits marking _ _ _ _ _ _ _
    markingInstruction
  have markingNext := M.next_step (decisionData input) bits marking _ _ _ _ _ _ _ markingInstruction
  have copyingObservation := boot_copy_observe program control alphabet input bits copying rfl
  have runZero : M.run (decisionData input) bits 0 = .running initial := initialObservation
  have runOne : M.run (decisionData input) bits 1 = .running marking := by
    rw [Machine.run, runZero]
    dsimp only
    rw [initialNext]
    exact markingObservation
  refine ⟨copying, ?_, rfl, ?_, ?_, ?_, rfl⟩
  · rw [Machine.run, runOne]
    dsimp only
    rw [markingNext]
    exact copyingObservation
  · simp [copying, marking, initial, Machine.stepConfiguration, Machine.initialConfiguration,
      Move.onInt]
  · simp [copying, marking, initial, Machine.stepConfiguration, Machine.initialConfiguration,
      Move.onInput]
  · funext i
    have outside : ¬ (0 ≤ i ∧ i < (0 : ℤ)) := by omega
    simp [copying, marking, initial, Machine.stepConfiguration, Machine.initialConfiguration,
      Move.onInt, bootMemory, outside, Function.update_apply]
    rfl

/-- Copying an input of length `n` costs `n` transitions after the two marker
initialization transitions. No arbitrary computation is hidden in the copy phase. -/
theorem boot_copy_complete (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) (k : ℕ)
    (bound : k ≤ input.length) :
    ∃ target, (postMachine program control alphabet).run (decisionData input) bits (k + 2) =
      .running target ∧ CopyRelated program control alphabet input k target := by
  induction k with
  | zero => exact boot_copy_initial program control alphabet input bits
  | succ k ih =>
      have available : k < input.length := by omega
      obtain ⟨target, run, related⟩ := ih (by omega)
      obtain ⟨nextTarget, next, nextRelated⟩ :=
        boot_copy_step program control alphabet input bits k target related available
      have observation := boot_copy_observe program control alphabet input bits nextTarget nextRelated.1
      refine ⟨nextTarget, ?_, nextRelated⟩
      have clock : k + 1 + 2 = (k + 2) + 1 := by omega
      rw [clock, Machine.run, run]
      simp only [next, observation]

omit [Fintype Γ] in
theorem bootMemory_input (alphabet : Γ ≃ Fin symbols) (input : List Γ) (i : ℤ) :
    bootDecode alphabet (bootMemory alphabet input input.length i) = (Tape.mk₁ input).nth i := by
  cases i with
  | ofNat n =>
      have not_marker : (n : ℤ) ≠ -1 := by omega
      by_cases available : n < input.length
      · simp [bootMemory, not_marker, available, Tape.mk₁, Tape.mk₂,
          ListBlank.nth_mk, ← List.getD_default_eq_getI]
      · simp [bootMemory, not_marker, available, bootDecode, Tape.mk₁, Tape.mk₂,
          ListBlank.nth_mk, ← List.getD_default_eq_getI]
  | negSucc n =>
      by_cases marker : Int.negSucc n = -1
      · simp [bootMemory, marker, Tape.mk₁, Tape.mk₂, Tape.mk', Tape.nth, ListBlank.nth_mk]
      · simp [bootMemory, marker, bootDecode, Tape.mk₁, Tape.mk₂, Tape.mk',
          Tape.nth, ListBlank.nth_mk]

omit [Fintype Γ] in
theorem bootMemory_not_marker (alphabet : Γ ≃ Fin symbols) (input : List Γ)
    (r : ℕ) (available : r < input.length) :
    bootMemory alphabet input input.length (r : ℤ) ≠ some (Fin.last symbols) := by
  have not_marker : (r : ℤ) ≠ -1 := by omega
  simp only [bootMemory, ite_eq_right not_marker]
  have inside : 0 ≤ (r : ℤ) ∧ (r : ℤ) < (input.length : ℤ) := by omega
  rw [ite_eq_left inside]
  intro equality
  have values := congrArg Fin.val (Option.some.inj equality)
  have bound := (alphabet (input.getD r default)).isLt
  simp only [bootEncode, Fin.val_castSucc, Fin.val_last] at values
  omega

def RewindRelated (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (r : ℕ)
    (target : Configuration (postMachine program control alphabet)) : Prop :=
  target.state = bootState 3 ∧ target.workHead = (r : ℤ) - 1 ∧
    target.work = bootMemory alphabet input input.length ∧ target.output = []

theorem boot_rewind_observe (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString)
    (target : Configuration (postMachine program control alphabet))
    (state : target.state = bootState 3) :
    (postMachine program control alphabet).observe (decisionData input) bits target =
      .running target := by
  simp [Machine.observe, postMachine, bootTransition, bootState, state]
  split_ifs <;> rfl

theorem boot_rewind_start (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) :
    ∃ target, (postMachine program control alphabet).run (decisionData input) bits (input.length + 3) =
      .running target ∧ RewindRelated program control alphabet input input.length target := by
  obtain ⟨copying, run, state, head, inputHead, memory, output⟩ :=
    boot_copy_complete program control alphabet input bits input.length (by rfl)
  let M := postMachine program control alphabet
  let rewinding := M.stepConfiguration (decisionData input) copying (bootState 3)
    none .left .stay .stay .stay none
  have instruction : M.transition copying.state input[copying.inputHead]?
      (decisionData input).auxiliary[copying.auxiliaryHead]?
      (if copying.indexHead < (decisionData input).index then some true else none)
      (copying.work copying.workHead) = .step (bootState 3) none .left .stay .stay .stay none := by
    simp [M, postMachine, bootTransition, state, inputHead, bootState]
  have next := M.next_step (decisionData input) bits copying _ _ _ _ _ _ _ instruction
  have observation := boot_rewind_observe program control alphabet input bits rewinding rfl
  refine ⟨rewinding, ?_, rfl, ?_, memory, output⟩
  · change M.run (decisionData input) bits ((input.length + 2) + 1) = _
    rw [Machine.run, run]
    simp only [next]
    exact observation
  · simp [rewinding, Machine.stepConfiguration, Move.onInt, head]

/-- Rewinding uses one transition per input symbol and one final transition
past the marker. The resulting tape is exactly Mathlib's source input tape. -/
theorem boot_rewind_complete (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) (r : ℕ)
    (bound : r ≤ input.length)
    (target : Configuration (postMachine program control alphabet))
    (related : RewindRelated program control alphabet input r target) :
    ∃ ready, PostRelated (postMachineSimulator program control alphabet) (TM0.init input) ready ∧
      (postMachine program control alphabet).runFrom (decisionData input) bits target (r + 1) =
        (postMachine program control alphabet).observe (decisionData input) bits ready := by
  let M := postMachine program control alphabet
  induction r generalizing target with
  | zero =>
      obtain ⟨state, head, memory, output⟩ := related
      have marker : target.work target.workHead = some (Fin.last symbols) := by
        simp [memory, head, bootMemory]
        rfl
      let ready := M.stepConfiguration (decisionData input) target (bootControl control default)
        none .right .stay .stay .stay none
      have instruction : M.transition target.state input[target.inputHead]?
          (decisionData input).auxiliary[target.auxiliaryHead]?
          (if target.indexHead < (decisionData input).index then some true else none)
          (target.work target.workHead) =
            .step (bootControl control default) none .right .stay .stay .stay none := by
        simp [M, postMachine, bootTransition, state, bootState, marker]
      have observation := boot_rewind_observe program control alphabet input bits target state
      have next := M.next_step (decisionData input) bits target _ _ _ _ _ _ _ instruction
      refine ⟨ready, ⟨rfl, output, ?_⟩, ?_⟩
      · intro i
        change bootDecode alphabet (target.work ((target.workHead + 1) + i)) = _
        have position : (target.workHead + 1) + i = i := by rw [head]; omega
        rw [position, memory]
        exact bootMemory_input alphabet input i
      · exact M.runFrom_shift (decisionData input) bits target ready observation next 0
  | succ r ih =>
      obtain ⟨state, head, memory, output⟩ := related
      have available : r < input.length := by omega
      have unmarked : target.work target.workHead ≠ some (Fin.last symbols) := by
        have position : ((r + 1 : ℕ) : ℤ) - 1 = (r : ℤ) := by omega
        rw [memory, head, position]
        exact bootMemory_not_marker alphabet input r available
      let nextTarget := M.stepConfiguration (decisionData input) target (bootState 3)
        none .left .stay .stay .stay none
      have instruction : M.transition target.state input[target.inputHead]?
          (decisionData input).auxiliary[target.auxiliaryHead]?
          (if target.indexHead < (decisionData input).index then some true else none)
          (target.work target.workHead) = .step (bootState 3) none .left .stay .stay .stay none := by
        simp [M, postMachine, bootTransition, state, bootState]
        exact unmarked
      have observation := boot_rewind_observe program control alphabet input bits target state
      have next := M.next_step (decisionData input) bits target _ _ _ _ _ _ _ instruction
      have nextRelated : RewindRelated program control alphabet input r nextTarget := by
        refine ⟨rfl, ?_, memory, output⟩
        change target.workHead - 1 = (r : ℤ) - 1
        rw [head]
        omega
      obtain ⟨ready, finalRelated, run⟩ := ih (by omega) nextTarget nextRelated
      refine ⟨ready, finalRelated, ?_⟩
      exact (M.runFrom_shift (decisionData input) bits target nextTarget observation next (r + 1)).trans run

/-- A concrete compiler from a finite Post machine to the paper's machine
model, including its initially blank work tape. Input loading takes `2n + 4`
transitions; subsequent source transitions are simulated one for one. -/
theorem postMachine_bootstrap (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) :
    ∃ ready, PostRelated (postMachineSimulator program control alphabet) (TM0.init input) ready ∧
      (postMachine program control alphabet).run (decisionData input) bits (2 * input.length + 4) =
        (postMachine program control alphabet).observe (decisionData input) bits ready := by
  obtain ⟨target, run, related⟩ := boot_rewind_start program control alphabet input bits
  obtain ⟨ready, readyRelated, finish⟩ :=
    boot_rewind_complete program control alphabet input bits input.length (by rfl) target related
  let M := postMachine program control alphabet
  have observation := boot_rewind_observe program control alphabet input bits target related.1
  have prefixRun : M.runFrom (decisionData input) bits M.initialConfiguration (input.length + 3) =
      M.observe (decisionData input) bits target := by rw [Machine.runFrom_initial, run, observation]
  have composed := M.runFrom_add (decisionData input) bits M.initialConfiguration target
    (input.length + 3) prefixRun (input.length + 1)
  refine ⟨ready, readyRelated, ?_⟩
  have clock : 2 * input.length + 4 = (input.length + 3) + (input.length + 1) := by omega
  rw [clock, ← Machine.runFrom_initial, composed]
  exact finish

omit [Fintype Γ] in
theorem bootTransition_deterministic (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (q : Fin (states + 4)) (input : Option Γ)
    (work : Option (Fin (symbols + 1))) :
    match bootTransition program control alphabet q input work with
    | .readRandom _ _ => False
    | _ => True := by
  unfold bootTransition
  by_cases phase : q.val < 4
  · simp only [dite_eq_left phase]
    interval_cases position : q.val
    · trivial
    · trivial
    · cases input <;> trivial
    · by_cases marker : work = some (Fin.last symbols)
      · simp [marker]
      · simp [marker]
  · simp only [dite_eq_right phase]
    cases instruction : program (control.symm (q.subNat 4 (by omega))) (bootDecode alphabet work) with
    | none => trivial
    | some action =>
        obtain ⟨next, action⟩ := action
        cases action <;> trivial

theorem postMachine_deterministic (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) : (postMachine program control alphabet).Deterministic := by
  intro q input auxiliary index work
  have nonRandom := bootTransition_deterministic program control alphabet q input work
  simp only [postMachine]
  cases instruction : bootTransition program control alphabet q input work <;>
    simp only [instruction] at nonRandom ⊢

/-- Acceptance equivalence for the actual compiled machine, started with the
paper's blank work tape. This quantifies over every finite random tape, though
the compiler is deterministic and never reads it. -/
theorem postMachine_accepts_iff (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) :
    (postMachine program control alphabet).Accepts (decisionData input) bits ↔
      ∃ last : TM0.Cfg Γ Q, TM0.Reaches program (TM0.init input) last ∧
        program last.q last.Tape.head = none := by
  let M := postMachine program control alphabet
  let sim := postMachineSimulator program control alphabet
  obtain ⟨ready, related, bootstrap⟩ := postMachine_bootstrap program control alphabet input bits
  have prefixRun : M.runFrom (decisionData input) bits M.initialConfiguration
      (2 * input.length + 4) = M.observe (decisionData input) bits ready := by
    rw [Machine.runFrom_initial]
    exact bootstrap
  have suffix (t : ℕ) : M.run (decisionData input) bits ((2 * input.length + 4) + t) =
      M.runFrom (decisionData input) bits ready t := by
    rw [← Machine.runFrom_initial]
    exact M.runFrom_add (decisionData input) bits M.initialConfiguration ready _ prefixRun t
  constructor
  · rintro ⟨word, t, accepted⟩
    have later := M.run_halted_add (decisionData input) bits t (.accepted word) accepted
      (2 * input.length + 4)
    rw [Nat.add_comm t, suffix] at later
    have empty := postSimulator_accepted_output sim (decisionData input) bits (TM0.init input)
      ready related t word later
    subst word
    exact (postSimulator_halting_iff sim (decisionData input) bits (TM0.init input) ready related).mp
      ⟨t, later⟩
  · intro halted
    obtain ⟨t, accepted⟩ :=
      (postSimulator_halting_iff sim (decisionData input) bits (TM0.init input) ready related).mpr halted
    exact ⟨[], (2 * input.length + 4) + t, (suffix t).trans accepted⟩

/-- Interface to Mathlib's partial evaluation semantics. The construction and
both directions of the simulation have proofs; no model-equivalence assumption
is required for this compiler. -/
theorem postMachine_accepts_iff_eval (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) (input : List Γ) (bits : BitString) :
    (postMachine program control alphabet).Accepts (decisionData input) bits ↔
      (TM0.eval program input).Dom := by
  rw [postMachine_accepts_iff]
  change (∃ last : TM0.Cfg Γ Q, TM0.Reaches program (TM0.init input) last ∧
    program last.q last.Tape.head = none) ↔
    (StateTransition.eval (TM0.step program) (TM0.init input)).Dom
  rw [Part.dom_iff_mem]
  apply exists_congr
  intro last
  rw [StateTransition.mem_eval]
  have stopped : TM0.step program last = none ↔ program last.q last.Tape.head = none := by
    simp [TM0.step]
  exact and_congr_right fun _ => stopped.symm

end ComplexityOfGenerators.Simulation
