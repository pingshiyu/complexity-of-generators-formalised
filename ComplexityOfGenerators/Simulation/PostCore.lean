import ComplexityOfGenerators.Foundations.RandomTape
import Mathlib.Computability.TuringMachine.PostTuringMachine
import Mathlib.Data.Fintype.EquivFin

/-!
# Executing Mathlib Post machines in the existing finite-control model

The compiler below has a genuinely finite transition table. Every Mathlib TM0
move or write is one native transition; blank writes are represented by an
explicit work symbol. Source and target tapes are related relative to the native
work head using Mathlib's proved tape lemmas.

This module verifies the execution core from a prepared configuration. Loading
an input into the native initially blank work tape is a separate bootstrap step;
the core does not pretend that an arbitrary initial work tape is a valid native
machine input.
-/

namespace ComplexityOfGenerators.Simulation

open Turing

variable {Γ Q : Type} [Fintype Γ] [Inhabited Γ] [Inhabited Q]
variable {states symbols : ℕ}

def decodeWork (alphabet : Γ ≃ Fin symbols) (work : Option (Fin symbols)) : Γ :=
  (work.map alphabet.symm).getD default

def postMove : Turing.Dir → Move
  | .left => .left
  | .right => .right

/-- TM0 halting is accepting here. To recognize a predicate, the source Post
program must halt exactly on that predicate, as in Mathlib's partial-recursive
recognizers. Programs rejecting by halting are not silently accepted as recognizers. -/
def postInstruction (control : Q → Fin states) (alphabet : Γ → Fin symbols) :
    Option (Q × TM0.Stmt Γ) → Instruction Unit states symbols
  | none => .accept
  | some (q, .move dir) => .step (control q) none (postMove dir) .stay .stay .stay none
  | some (q, .write symbol) => .step (control q) (some (alphabet symbol))
      .stay .stay .stay .stay none

def postCore (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) : Machine Γ Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := states
  symbols := symbols
  initial := control default
  transition := fun q _ _ _ work =>
    postInstruction control alphabet (program (control.symm q) (decodeWork alphabet work))

theorem postCore_deterministic (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) : (postCore program control alphabet).Deterministic := by
  intro q input auxiliary index work
  simp only [postCore]
  cases program (control.symm q) (decodeWork alphabet work) with
  | none => trivial
  | some action =>
      obtain ⟨q', action⟩ := action
      cases action <;> trivial

/-- A finite instruction-table implementation of a source Post program.
The fields describe a concrete transition-table equality, not a halting or
complexity assumption. Actual implementations are constructed below. -/
structure PostSimulator (program : TM0.Machine Γ Q) (I : Type := Γ) where
  machine : Machine I Bool Unit
  control : Q → Fin machine.states
  encode : Γ → Fin machine.symbols
  decode : Option (Fin machine.symbols) → Γ
  writeCorrect : ∀ symbol, decode (some (encode symbol)) = symbol
  transitionCorrect : ∀ q input auxiliary index work,
    machine.transition (control q) input auxiliary index work =
      postInstruction control encode (program q (decode work))

variable {program : TM0.Machine Γ Q}

/-- The original finite-control execution core is an implementation, with every
simulation field proved from its actual transition table. -/
def postCoreSimulator (program : TM0.Machine Γ Q) (control : Q ≃ Fin states)
    (alphabet : Γ ≃ Fin symbols) : PostSimulator program where
  machine := postCore program control alphabet
  control := control
  encode := alphabet
  decode := decodeWork alphabet
  writeCorrect := by
    intro symbol
    change alphabet.symm (alphabet symbol) = symbol
    exact alphabet.symm_apply_apply symbol
  transitionCorrect := by intros; simp [postCore]

omit [Fintype Γ]

variable {I : Type}

def PostRelated (sim : PostSimulator program I) (source : TM0.Cfg Γ Q)
    (target : Configuration sim.machine) : Prop :=
  target.state = sim.control source.q ∧ target.output = [] ∧
    ∀ i : ℤ, sim.decode (target.work (target.workHead + i)) = source.Tape.nth i

theorem postSimulator_observe_halted (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source : TM0.Cfg Γ Q)
    (target : Configuration sim.machine)
    (related : PostRelated sim source target)
    (halted : program source.q source.Tape.head = none) :
    sim.machine.observe data bits target = .halted (.accepted []) := by
  obtain ⟨state, output, tape⟩ := related
  have head := tape 0
  simp only [add_zero, Tape.nth_zero] at head
  simp [Machine.observe, state, sim.transitionCorrect, head, halted, postInstruction, output]

theorem postSimulator_observe_halted_iff (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source : TM0.Cfg Γ Q)
    (target : Configuration sim.machine)
    (related : PostRelated sim source target) :
    sim.machine.observe data bits target = .halted (.accepted []) ↔
      program source.q source.Tape.head = none := by
  obtain ⟨state, output, tape⟩ := related
  have head := tape 0
  simp only [add_zero, Tape.nth_zero] at head
  cases instruction : program source.q source.Tape.head with
  | none => simp [Machine.observe, state, sim.transitionCorrect, head, instruction, postInstruction, output]
  | some action =>
      obtain ⟨q, action⟩ := action
      cases action <;> simp [Machine.observe, state, sim.transitionCorrect, head, instruction, postInstruction]

/-- One source step is implemented by one target step, with no hidden evaluation
inside the target instruction. The visited-cell accounting is updated by `next`. -/
theorem postSimulator_step (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source nextSource : TM0.Cfg Γ Q)
    (target : Configuration sim.machine)
    (related : PostRelated sim source target)
    (step : TM0.step program source = some nextSource) :
    sim.machine.observe data bits target = .running target ∧
      ∃ nextTarget,
        sim.machine.next data bits target = .running nextTarget ∧
          PostRelated sim nextSource nextTarget := by
  obtain ⟨state, output, tape⟩ := related
  have head := tape 0
  simp only [add_zero, Tape.nth_zero] at head
  unfold TM0.step at step
  obtain ⟨⟨q, action⟩, instruction, rfl⟩ := Option.map_eq_some_iff.mp step
  cases action with
  | move dir =>
      constructor
      · simp [Machine.observe, state, sim.transitionCorrect, head, instruction, postInstruction]
      · simp only [Machine.next, state, sim.transitionCorrect, head,
          instruction, postInstruction]
        refine ⟨_, rfl, rfl, output, ?_⟩
        intro i
        cases dir with
        | left => simpa [postMove, Move.onInt, sub_add_eq_add_sub, add_sub_assoc] using tape (i - 1)
        | right => simpa [postMove, Move.onInt, add_assoc, add_comm, add_left_comm] using tape (i + 1)
  | write symbol =>
      constructor
      · simp [Machine.observe, state, sim.transitionCorrect, head, instruction, postInstruction]
      · simp only [Machine.next, state, sim.transitionCorrect, head,
          instruction, postInstruction]
        refine ⟨_, rfl, rfl, output, ?_⟩
        intro i
        by_cases origin : i = 0
        · subst i
          simp [Move.onInt, sim.writeCorrect, Tape.write]
        · have different : target.workHead + i ≠ target.workHead := by omega
          simpa [Move.onInt, Function.update_of_ne different, Tape.write_nth, origin]
            using tape i

/-- Finite source executions are implemented by finite native executions, with
one native transition for each source transition. The source tape is not flattened
into an arbitrary function during execution: only one cell is inspected per step. -/
theorem postSimulator_reaches (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source last : TM0.Cfg Γ Q)
    (target : Configuration sim.machine)
    (related : PostRelated sim source target)
    (path : TM0.Reaches program source last) :
    ∃ t nextTarget, PostRelated sim last nextTarget ∧
      sim.machine.runFrom data bits target t =
        sim.machine.observe data bits nextTarget := by
  induction path with
  | refl => exact ⟨0, target, related, rfl⟩
  | @tail current last path step ih =>
      obtain ⟨t, currentTarget, currentRelated, simulation⟩ := ih
      obtain ⟨live, nextTarget, next, nextRelated⟩ :=
        postSimulator_step sim data bits current last currentTarget currentRelated
          (Option.mem_def.mp step)
      refine ⟨t + 1, nextTarget, nextRelated, ?_⟩
      simp only [Machine.runFrom, simulation, live, next]

theorem postSimulator_halts_of_reaches (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source last : TM0.Cfg Γ Q)
    (target : Configuration sim.machine)
    (related : PostRelated sim source target)
    (path : TM0.Reaches program source last)
    (halted : program last.q last.Tape.head = none) :
    ∃ t, sim.machine.runFrom data bits target t = .halted (.accepted []) := by
  obtain ⟨t, lastTarget, lastRelated, simulation⟩ :=
    postSimulator_reaches sim data bits source last target related path
  exact ⟨t, simulation.trans
    (postSimulator_observe_halted sim data bits last lastTarget lastRelated halted)⟩

/-- The native core cannot accept spuriously: every accepting execution comes
from a halting execution of the source Post machine. -/
theorem postSimulator_reaches_of_halted (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source : TM0.Cfg Γ Q)
    (target : Configuration sim.machine)
    (related : PostRelated sim source target) (t : ℕ)
    (halted : sim.machine.runFrom data bits target t =
      .halted (.accepted [])) :
    ∃ last : TM0.Cfg Γ Q, TM0.Reaches program source last ∧
      program last.q last.Tape.head = none := by
  induction t generalizing source target with
  | zero =>
      exact ⟨source, .refl,
        (postSimulator_observe_halted_iff sim data bits source target related).mp halted⟩
  | succ t ih =>
      cases instruction : program source.q source.Tape.head with
      | none => exact ⟨source, .refl, instruction⟩
      | some action =>
          let nextSource : TM0.Cfg Γ Q := ⟨action.1, match action.2 with
            | .move dir => source.Tape.move dir
            | .write symbol => source.Tape.write symbol⟩
          have sourceStep : TM0.step program source = some nextSource := by
            simp [TM0.step, instruction, nextSource]
            rfl
          obtain ⟨live, nextTarget, next, nextRelated⟩ :=
            postSimulator_step sim data bits source nextSource target related sourceStep
          rw [sim.machine.runFrom_shift data bits target nextTarget live next t]
            at halted
          obtain ⟨last, path, lastHalted⟩ := ih nextSource nextTarget nextRelated halted
          have first : TM0.Reaches program source nextSource :=
            Relation.ReflTransGen.single (by simp [sourceStep])
          exact ⟨last, first.trans path, lastHalted⟩

theorem postSimulator_halting_iff (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source : TM0.Cfg Γ Q)
    (target : Configuration sim.machine)
    (related : PostRelated sim source target) :
    (∃ t, sim.machine.runFrom data bits target t = .halted (.accepted [])) ↔
      ∃ last : TM0.Cfg Γ Q, TM0.Reaches program source last ∧
        program last.q last.Tape.head = none := by
  constructor
  · rintro ⟨t, halted⟩
    exact postSimulator_reaches_of_halted sim data bits source target related t halted
  · rintro ⟨last, path, halted⟩
    exact postSimulator_halts_of_reaches sim data bits source last target related path halted

/-- The simulator emits no output, even on executions which have not yet
been shown to correspond to a halting source execution. -/
theorem postSimulator_accepted_output (sim : PostSimulator program I)
    (data : InputData I Bool) (bits : BitString) (source : TM0.Cfg Γ Q)
    (target : Configuration sim.machine) (related : PostRelated sim source target)
    (t : ℕ) (word : List Unit)
    (accepted : sim.machine.runFrom data bits target t = .halted (.accepted word)) : word = [] := by
  induction t generalizing source target with
  | zero =>
      obtain ⟨state, output, tape⟩ := related
      have head := tape 0
      simp only [add_zero, Tape.nth_zero] at head
      cases instruction : program source.q source.Tape.head with
      | none =>
          simp [Machine.runFrom, Machine.observe, state, sim.transitionCorrect, head,
            instruction, postInstruction, output] at accepted
          exact accepted
      | some action =>
          obtain ⟨q, action⟩ := action
          cases action <;>
            simp [Machine.runFrom, Machine.observe, state, sim.transitionCorrect, head,
              instruction, postInstruction] at accepted
  | succ t ih =>
      cases instruction : program source.q source.Tape.head with
      | none =>
          have observation := postSimulator_observe_halted sim data bits source target related instruction
          have empty := sim.machine.runFrom_halted data bits target (.accepted []) observation (t + 1)
          rw [empty] at accepted
          exact (Outcome.accepted.inj (RunState.halted.inj accepted)).symm
      | some action =>
          let nextSource : TM0.Cfg Γ Q := ⟨action.1, match action.2 with
            | .move dir => source.Tape.move dir
            | .write symbol => source.Tape.write symbol⟩
          have sourceStep : TM0.step program source = some nextSource := by
            simp [TM0.step, instruction, nextSource]
            rfl
          obtain ⟨live, nextTarget, next, nextRelated⟩ :=
            postSimulator_step sim data bits source nextSource target related sourceStep
          rw [sim.machine.runFrom_shift data bits target nextTarget live next t] at accepted
          exact ih nextSource nextTarget nextRelated accepted

end ComplexityOfGenerators.Simulation
