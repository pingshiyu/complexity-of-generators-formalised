import ComplexityOfGenerators.Simulation.WordStack.LengthTest
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare
import ComplexityOfGenerators.Simulation.WordStack.RandomFree
import ComplexityOfGenerators.Examples.HAMPATHInverseWords

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Position

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 3000

abbrev Store := Local.Store Symbol 12

/-- A malformed sampled position uses a fixed valid endpoint. Thus sampling
positions never introduces rejection once the target label is admissible. -/
def value (size start next candidate : ℕ) : Option ℕ :=
  if next = start then some (if start < candidate ∧ candidate ≤ size then candidate else size)
  else if next = start+1 then some (if candidate ≤ start then candidate else 0)
  else none

def equalSlots : LengthTest.Layout 12 := ⟨![2, 1, 6, 7, 8, 9], by decide⟩
def successorSlots : LengthTest.Layout 12 := ⟨![2, 10, 6, 7, 8, 9], by decide⟩
def lowerSlots : RationalSelection.Compare.Layout 12 := ⟨![3, 1, 6, 7, 8, 9], by decide⟩
def upperSlots : RationalSelection.Compare.Layout 12 := ⟨![3, 0, 6, 7, 8, 9], by decide⟩

def copy {O : Type} (source : Fin 12) (different : source ≠ 4) (scratch : source ≠ 11) : Routine Symbol O 12 :=
  Routine.assign source 4 11 different scratch (by decide) (fun _ => .bit true)

def right {O : Type} : Routine Symbol O 12 :=
  (RationalSelection.Compare.routine lowerSlots (.bit true)).seq
    (Routine.branch 6 fun above => if above.isSome then
      (RationalSelection.Compare.routine upperSlots (.bit true)).seq
        (Routine.branch 6 fun tooLarge => if tooLarge.isSome then copy 0 (by decide) (by decide)
          else copy 3 (by decide) (by decide))
      else copy 0 (by decide) (by decide))

def left {O : Type} : Routine Symbol O 12 :=
  (RationalSelection.Compare.routine lowerSlots (.bit true)).seq
    (Routine.branch 6 fun above => if above.isSome then Routine.clear 4
      else copy 3 (by decide) (by decide))

def mark {O : Type} : Routine Symbol O 12 := Routine.ofLocal (Local.push 5 (.bit true))

def successor {O : Type} : Routine Symbol O 12 :=
  (Routine.assign 1 10 11 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
    ((Routine.ofLocal (Local.push 10 (.bit true))).seq
      ((LengthTest.routine successorSlots (.bit true)).seq
        (Routine.branch 6 fun equal => if equal.isSome then left.seq mark else Routine.skip)))

def routine {O : Type} : Routine Symbol O 12 :=
  (Routine.clearMany [4, 5]).seq
    ((LengthTest.routine equalSlots (.bit true)).seq
      (Routine.branch 6 fun equal => if equal.isSome then right.seq mark else successor))

theorem routine_values {O : Type} (s : Store) :
    (routine (O := O)).eval s 4 =
        List.replicate ((value (s 0).length (s 1).length (s 2).length (s 3).length).getD 0) (.bit true) ∧
      ((routine (O := O)).eval s 5).head?.isSome =
        (value (s 0).length (s 1).length (s 2).length (s 3).length).isSome := by
  by_cases equal : (s 2).length = (s 1).length <;>
    by_cases successorEq : (s 2).length = (s 1).length+1 <;>
    by_cases lower : (s 3).length ≤ (s 1).length <;>
    by_cases upper : (s 3).length ≤ (s 0).length <;>
    simp [routine, Routine.seq, Routine.clearMany_eval, LengthTest.routine_eval,
      Routine.branch, right, left, successor, copy, Routine.assign_eval, mark,
      Routine.ofLocal, Local.eval_push, Routine.clear, Routine.skip,
      RationalSelection.Compare.routine_eval, equalSlots, successorSlots, lowerSlots, upperSlots,
      value, equal, successorEq, lower, upper, show (s 1).length < (s 3).length ↔ ¬ (s 3).length ≤ (s 1).length from by omega,
      show (s 0).length < (s 3).length ↔ ¬ (s 3).length ≤ (s 0).length from by omega]

theorem value_sound (size start next candidate chosen : ℕ) (inside : start < size)
    (selected : value size start next candidate = some chosen) :
    chosen ≤ size ∧ expand chosen start = next := by
  unfold value at selected
  split_ifs at selected <;> simp only [Option.some.injEq, reduceCtorEq] at selected
  all_goals subst chosen; constructor
  all_goals first | omega | (unfold expand; split_ifs <;> omega)

theorem value_complete (size start position : ℕ) (inside : start < size) (fits : position ≤ size) :
    value size start (expand position start) position = some position := by
  by_cases before : start < position
  · simp [value, expand, before, fits]
  · have bound : position ≤ start := by omega
    simp [value, expand, before, bound]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Position
