import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Output.Basic
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Productive
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelModel
import ComplexityOfGenerators.Examples.HAMPATHNative.Metadata

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Output.Store

def require (source : Fin 64) (expected : Bool) : Routine Symbol Symbol 64 :=
  Routine.branch source fun found => if found.isSome = expected then Routine.skip else Routine.clear 41

theorem require_eval (source : Fin 64) (expected : Bool) (s : Store) :
    (require source expected).eval s = Function.update s 41
      (if (s source).head?.isSome = expected then s 41 else []) := by
  simp only [require,Routine.branch]
  split <;> simp [Routine.skip,Routine.ofLocal,Routine.clear,Function.update_eq_self]

noncomputable def parse : Routine Symbol Symbol 64 :=
  (Routine.assign 32 2 48 (by decide) (by decide) (by decide) id).seq
    (((parser (O := Symbol)).rename Output.low32).seq
      ((Routine.assign 4 35 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
        (Routine.assign 13 36 48 (by decide) (by decide) (by decide) (fun _ => .bit true))))

noncomputable def productive : Routine Symbol Symbol 64 :=
  (Routine.assign 34 12 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
    ((Productive.routine.rename Output.low16).seq
      (Routine.assign 11 41 48 (by decide) (by decide) (by decide) (fun _ => .bit true)))

noncomputable def parent : Routine Symbol Symbol 64 :=
  (Routine.assign 35 17 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
    ((Routine.ofLocal (Local.push 17 (.bit true))).seq
      (((Logarithm.routine (O := Symbol)).rename Output.low32).seq
        ((Routine.assign 17 37 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
          (Routine.assign 19 38 48 (by decide) (by decide) (by decide) (fun _ => .bit true)))))

def counterSlots : CounterRoutine.Layout 64 := ⟨![37,46,47,48,49], by decide⟩
def capacitySlots : RationalSelection.Compare.Layout 64 := ⟨![46,34,20,21,22,23], by decide⟩
def singletonSlots : LengthTest.Layout 64 := ⟨![35,49,20,21,22,23], by decide⟩

def capacity : Routine Symbol Symbol 64 :=
  (CounterRoutine.routine counterSlots BaseSearch.square (.bit true)).seq
    ((Routine.ofLocal (Local.push 46 (.bit true))).seq
      ((RationalSelection.Compare.routine capacitySlots (.bit true)).seq (require 20 false)))

def singleton : Routine Symbol Symbol 64 :=
  (Routine.clear 49).seq
    ((Routine.ofLocal (Local.push 49 (.bit true))).seq
      ((LengthTest.routine singletonSlots (.bit true)).seq (require 20 true)))

def labelPrepare : Routine Symbol Symbol 64 :=
  (Routine.assign 33 25 48 (by decide) (by decide) (by decide) id).seq
    ((Routine.assign 38 19 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      ((Routine.assign 37 27 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
        ((Routine.assign 37 26 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
          ((Routine.clear 16).seq (Routine.ofLocal (Local.push 16 (.bit true)))))))

noncomputable def label : Routine Symbol Symbol 64 :=
  labelPrepare.seq
    (((LabelBits.routine (O := Symbol)).rename Output.low32).seq
      (((LabelChecks.routine (O := Symbol)).rename Output.low32).seq
        ((Routine.assign 28 39 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
          (require 16 true))))

noncomputable def routine : Routine Symbol Symbol 64 :=
  parse.seq (productive.seq (parent.seq
    (Routine.branch 33 fun word => if word.isNone then singleton else capacity.seq label)))

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Classify
