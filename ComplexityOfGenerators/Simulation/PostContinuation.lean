import ComplexityOfGenerators.Simulation.PostCore
import ComplexityOfGenerators.Simulation.RoutineComposition

/-! The concrete sequential machine simulates every Post computation up to its
halting configuration, then transfers its work tape to an output routine. -/

namespace ComplexityOfGenerators.Simulation

open Turing

set_option backward.isDefEq.respectTransparency false

variable {Γ Q I O : Type} [Inhabited Γ] [Inhabited Q] [Finite O]
variable {program : TM0.Machine Γ Q}

theorem sequence_post_reaches (sim : PostSimulator program I)
    (routine : Routine I Bool O sim.machine.symbols) (data : InputData I Bool) (bits : BitString)
    (source last : TM0.Cfg Γ Q) (target : Configuration sim.machine) (out : List O)
    (related : PostRelated sim source target) (path : TM0.Reaches program source last) :
    ∃ t final, PostRelated sim last final ∧
      (sequenceMachine sim.machine routine).runFrom data bits
        (sequenceLeftConfiguration sim.machine routine target out) t =
      (sequenceMachine sim.machine routine).observe data bits
        (sequenceLeftConfiguration sim.machine routine final out) := by
  induction path with
  | refl => exact ⟨0, target, related, rfl⟩
  | @tail current last path step ih =>
      obtain ⟨t, currentTarget, currentRelated, simulation⟩ := ih
      obtain ⟨live, nextTarget, next, nextRelated⟩ :=
        postSimulator_step sim data bits current last currentTarget currentRelated (Option.mem_def.mp step)
      have targetLive := sequence_left_observe sim.machine routine data bits currentTarget out live
      have targetNext := sequence_left_next sim.machine routine data bits currentTarget nextTarget out next
      refine ⟨t + 1, nextTarget, nextRelated, ?_⟩
      simp only [Machine.runFrom, simulation, targetLive, targetNext]

theorem sequence_post_handoff [Finite I] (sim : PostSimulator program I)
    (routine : Routine I Bool O sim.machine.symbols) (data : InputData I Bool) (bits : BitString)
    (source : TM0.Cfg Γ Q) (target : Configuration sim.machine) (out : List O)
    (related : PostRelated sim source target) (halted : program source.q source.Tape.head = none) :
    (sequenceMachine sim.machine routine).runFrom data bits
        (sequenceLeftConfiguration sim.machine routine target out) 1 =
      (sequenceMachine sim.machine routine).observe data bits
        (sequenceRightConfiguration sim.machine routine
          (handoffConfiguration sim.machine routine data target out)) := by
  obtain ⟨state, output, tape⟩ := related
  have head := tape 0
  simp only [add_zero, Tape.nth_zero] at head
  apply sequence_accept_handoff
  simp [state, sim.transitionCorrect, head, halted, postInstruction]

end ComplexityOfGenerators.Simulation
