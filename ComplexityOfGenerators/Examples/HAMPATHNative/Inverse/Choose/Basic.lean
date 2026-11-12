import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Classify.Fields
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Position
import ComplexityOfGenerators.Simulation.WordStack.TakeWord

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Output.Store

def low12 : Fin 12 ↪ Fin 64 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b same := Fin.ext (congrArg (fun j : Fin 64 => j.val) same)

def candidateSlots : TakeWord.Layout 64 := ⟨![42,38,25,46,47,48], by decide⟩
def incomingSlots : TakeWord.Layout 64 := ⟨![42,35,44,46,47,48], by decide⟩
def outgoingSlots : TakeWord.Layout 64 := ⟨![42,35,45,46,47,48], by decide⟩
def forceSlots : DropAt.Layout 64 := ⟨![45,36,46,47,48], by decide⟩

noncomputable def candidate : Routine Symbol Symbol 64 :=
  (TakeWord.routine candidateSlots).seq
    ((Routine.assign 38 19 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      (((LabelBits.routine (O := Symbol)).rename Output.low32).seq
        (Routine.assign 28 40 48 (by decide) (by decide) (by decide) (fun _ => .bit true))))

def incidents : Routine Symbol Symbol 64 :=
  (TakeWord.routine incomingSlots).seq (TakeWord.routine outgoingSlots)

def positionPrepare : Routine Symbol Symbol 64 :=
  (Routine.assign 35 0 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
    ((Routine.assign 36 1 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      ((Routine.assign 39 2 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
        (Routine.assign 40 3 48 (by decide) (by decide) (by decide) (fun _ => .bit true))))

noncomputable def position : Routine Symbol Symbol 64 :=
  positionPrepare.seq
    (((Position.routine (O := Symbol)).rename low12).seq
      ((Routine.assign 4 40 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
        (Classify.require 5 true)))

def forceEdge : Routine Symbol Symbol 64 :=
  (DropAt.routine forceSlots (.bit true)).seq
    (InsertAt.routine forceSlots (.bit true) (.bit true))

noncomputable def routine : Routine Symbol Symbol 64 :=
  candidate.seq (incidents.seq (position.seq forceEdge))

theorem routine_eval (s : Store) : routine.eval s =
    forceEdge.eval (position.eval (incidents.eval (candidate.eval s))) := rfl

attribute [irreducible] routine
attribute [irreducible] forceEdge

def sampleClock : Routine Symbol Symbol 64 :=
  (Routine.assign 38 46 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
    ((Routine.copy 35 46 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      (Routine.copy 35 46 48 (by decide) (by decide) (by decide) (fun _ => .bit true)))

theorem sampleClock_eval (s : Store) :
    sampleClock.eval s = Function.update (Function.update s 48 []) 46
      (List.replicate ((s 38).length+2*(s 35).length) (.bit true)) := by
  funext j
  by_cases clock : j=46
  · subst j
    simp [sampleClock,Routine.seq,Routine.assign_eval,Routine.copy,List.map_const',← List.replicate_add]
    omega
  · by_cases scratch : j=48 <;>
      simp [sampleClock,Routine.seq,Routine.assign_eval,Routine.copy,Function.update_apply,clock,scratch]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose
