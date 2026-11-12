import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Position
import ComplexityOfGenerators.Simulation.WordStack.RoutineResources

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Position

open Simulation.WordStack
open Routine

set_option backward.isDefEq.respectTransparency true

theorem copy_bound {O : Type} (source : Fin 12) (different : source≠4) (scratch : source≠11) (budget : ℕ) :
    ResourceBound (copy (O := O) source different scratch) budget budget (20*(budget+1)) :=
  ResourceBound.assign (S := Symbol) (O := O) source 4 11 different scratch (by decide) (fun _ => Symbol.bit true) budget

theorem right_bound {O : Type} (budget : ℕ) (positive : 1≤budget) :
    ResourceBound (right (O := O)) budget budget (400*(budget+1)) := by
  have choices : ResourceBound
      (Routine.branch 6 fun tooLarge : Option Symbol => if tooLarge.isSome then copy (O := O) 0 (by decide) (by decide)
        else copy 3 (by decide) (by decide)) budget budget (1+20*(budget+1)) := by
    apply ResourceBound.branch
    intro head
    split <;> exact copy_bound _ _ _ budget
  have upper := (ResourceBound.strictCompare (O := O) upperSlots (.bit true) budget positive).seq choices
  have upperBound := upper.weaken le_rfl le_rfl (show 80*(budget+1)+1+(1+20*(budget+1))≤200*(budget+1) by omega)
  have branches : ResourceBound
      (Routine.branch 6 fun above : Option Symbol => if above.isSome then
        (RationalSelection.Compare.routine (O := O) upperSlots (.bit true)).seq
          (Routine.branch 6 fun tooLarge => if tooLarge.isSome then copy 0 (by decide) (by decide) else copy 3 (by decide) (by decide))
        else copy 0 (by decide) (by decide)) budget budget (1+200*(budget+1)) := by
    apply ResourceBound.branch
    intro head
    split
    · exact upperBound
    · exact (copy_bound _ _ _ budget).weaken le_rfl le_rfl (by omega)
  have result := (ResourceBound.strictCompare (O := O) lowerSlots (.bit true) budget positive).seq branches
  exact result.weaken le_rfl le_rfl (by omega)

theorem left_bound {O : Type} (budget : ℕ) (positive : 1≤budget) :
    ResourceBound (left (O := O)) budget budget (200*(budget+1)) := by
  have branches : ResourceBound
      (Routine.branch 6 fun above : Option Symbol => if above.isSome then Routine.clear 4
        else copy (O := O) 3 (by decide) (by decide)) budget budget (1+20*(budget+1)) := by
    apply ResourceBound.branch
    intro head
    split
    · exact (ResourceBound.clear (O := O) 4 budget).weaken le_rfl le_rfl (by omega)
    · exact copy_bound _ _ _ budget
  have result := (ResourceBound.strictCompare (O := O) lowerSlots (.bit true) budget positive).seq branches
  exact result.weaken le_rfl le_rfl (by omega)

theorem successor_bound {O : Type} (budget : ℕ) (positive : 1≤budget) :
    ResourceBound (successor (O := O)) budget (budget+2) (1000*(budget+2)) := by
  have chosen := (left_bound (O := O) (budget+1) (by omega)).seq
    (ResourceBound.push (O := O) 5 (.bit true) (budget+1))
  have branches : ResourceBound
      (Routine.branch 6 fun equal : Option Symbol => if equal.isSome then (left (O := O)).seq mark else Routine.skip)
      (budget+1) (budget+2) (1+(200*(budget+2)+1+1)) := by
    apply ResourceBound.branch
    intro head
    split
    · exact chosen
    · exact (ResourceBound.skip (S := Symbol) (O := O) (k := 12) (budget+1)).weaken le_rfl (by omega) (by omega)
  have tested := (ResourceBound.lengthTest (O := O) successorSlots (.bit true) (budget+1) (by omega)).seq branches
  have pushed := (ResourceBound.push (O := O) 10 (.bit true) budget).seq tested
  have result := (ResourceBound.assign (O := O) 1 10 11 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true) budget).seq pushed
  exact result.weaken le_rfl le_rfl (by omega)

theorem routine_resources {O : Type} (budget : ℕ) (positive : 1≤budget) :
    ResourceBound (routine (O := O)) budget (budget+2) (2000*(budget+2)) := by
  have rightChosen := (right_bound (O := O) budget positive).seq
    (ResourceBound.push (O := O) 5 (.bit true) budget)
  have branches : ResourceBound
      (Routine.branch 6 fun equal : Option Symbol => if equal.isSome then (right (O := O)).seq mark else successor)
      budget (budget+2) (1+1000*(budget+2)) := by
    apply ResourceBound.branch
    intro head
    split
    · exact rightChosen.weaken le_rfl (by omega) (by omega)
    · exact successor_bound budget positive
  have tested := (ResourceBound.lengthTest (O := O) equalSlots (.bit true) budget positive).seq branches
  have result := (ResourceBound.clearMany (S := Symbol) (O := O) [4,5] budget).seq tested
  exact result.weaken le_rfl le_rfl (by simp only [List.length_cons,List.length_nil] at *; omega)

theorem routine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((routine (O := O)).eval s) (budget+3) ∧
      (routine (O := O)).cost s≤2000*(budget+3) :=
  routine_resources (budget+1) (by omega) s (sizes.mono (by omega))

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Position
