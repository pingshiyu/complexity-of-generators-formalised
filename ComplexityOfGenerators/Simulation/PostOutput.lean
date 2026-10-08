import ComplexityOfGenerators.Simulation.PostContinuation
import ComplexityOfGenerators.Simulation.OutputCorrectness

/-! A finite native Post simulator with a concrete word-output continuation.
This composes source execution, the one-step work-tape handoff and the proved
finite output routine. No arbitrary word-emitting computation is assumed. -/

namespace ComplexityOfGenerators.Simulation

open Turing

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α Q : Type} [Fintype α] [Encodable α] [Inhabited Q]
variable {program : TM0.Machine RecursiveAlphabet Q}

def postOutputRead (sim : PostSimulator program Unit) :
    Option (Fin sim.machine.symbols) → Option PartrecToTM2.Γ' :=
  fun work => (sim.decode work).2 PartrecToTM2.K'.main

def postOutputRoutine (sim : PostSimulator program Unit) : Routine Unit Bool α sim.machine.symbols where
  states := Fintype.card (OutputControl α)
  initial := outputControl .start
  transition := (outputMachine (α := α) sim.machine.symbols (postOutputRead sim)).transition

def postOutputMachine (sim : PostSimulator program Unit) : Machine Unit Bool α :=
  sequenceMachine sim.machine (postOutputRoutine (α := α) sim)

/-- A prepared native simulation of a terminating Post computation emits the
word represented by its final main stack. This is an execution theorem for the
concrete combined transition table, on every finite random tape. -/
theorem postOutputMachine_emits_word (sim : PostSimulator program Unit)
    (data : InputData Unit Bool) (bits : BitString) (word out : List α)
    (source last : TM0.Cfg RecursiveAlphabet Q) (target : Configuration sim.machine)
    (related : PostRelated sim source target) (path : TM0.Reaches program source last)
    (halted : program last.q last.Tape.head = none)
    (decoded : ∀ n : ℕ, (last.Tape.nth (n : ℤ)).2 PartrecToTM2.K'.main = (outputCells word)[n]?) :
    ∃ t, (postOutputMachine (α := α) sim).runFrom data bits
      (sequenceLeftConfiguration sim.machine (postOutputRoutine sim) target out) t =
        .halted (.accepted (out ++ word)) := by
  let routine := postOutputRoutine (α := α) sim
  let combined := sequenceMachine sim.machine routine
  obtain ⟨t, final, finalRelated, simulation⟩ :=
    sequence_post_reaches sim routine data bits source last target out related path
  let ready := handoffConfiguration sim.machine routine data final out
  have handoff := sequence_post_handoff sim routine data bits last final out finalRelated halted
  have outputReady : OutputReady (postOutputRead sim) .start (outputCells word) out ready := by
    refine ⟨rfl, rfl, ?_⟩
    intro n
    have tape := congrArg (fun symbol : RecursiveAlphabet => symbol.2 PartrecToTM2.K'.main)
      (finalRelated.2.2 (n : ℤ))
    exact tape.trans (decoded n)
  have emits := outputMachine_emits_word (postOutputRead sim) data bits word out ready outputReady
  have routineEmits : routine.machine.runFrom data bits ready ((outputCells word).length + 1) =
      .halted (.accepted (out ++ word)) := emits
  have nativeEmission := sequence_right_runFrom sim.machine routine data bits ready ((outputCells word).length + 1)
  rw [routineEmits] at nativeEmission
  change combined.runFrom data bits (sequenceRightConfiguration sim.machine routine ready)
    ((outputCells word).length + 1) = .halted (.accepted (out ++ word)) at nativeEmission
  refine ⟨t + (1 + ((outputCells word).length + 1)), ?_⟩
  have computation := combined.runFrom_add data bits
    (sequenceLeftConfiguration sim.machine routine target out)
    (sequenceLeftConfiguration sim.machine routine final out) t simulation
    (1 + ((outputCells word).length + 1))
  have output := combined.runFrom_add data bits
    (sequenceLeftConfiguration sim.machine routine final out)
    (sequenceRightConfiguration sim.machine routine ready) 1 handoff ((outputCells word).length + 1)
  exact computation.trans (output.trans nativeEmission)

end

end ComplexityOfGenerators.Simulation
