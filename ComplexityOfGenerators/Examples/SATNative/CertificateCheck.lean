import ComplexityOfGenerators.Examples.SATNative.AssignmentValue
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

instance binaryDecidable (word : List Symbol) : Decidable (Binary word) := by
  unfold Binary
  infer_instance

def isBit (symbol : Symbol) : Bool := decide (symbol = .zero ∨ symbol = .one)

def certificateSlots : LengthTest.Layout 32 := ⟨![3, 10, 27, 22, 23, 9], by decide⟩

def bitPrefix {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 24).seq
    ((Routine.assign 3 25 9 (by decide) (by decide) (by decide) id).seq
      (Routine.transferWhile 25 24 (by decide) isBit id))

def certificateCheck {O : Type} : Routine Symbol O 32 :=
  (LengthTest.routine certificateSlots .one).seq
    (bitPrefix.seq (Routine.ofLocal (LengthTest.finishCode 25 27)))

theorem bitPrefix_eval {O : Type} (s : Store) :
    (bitPrefix (O := O)).eval s =
      Function.update (Function.update (Function.update s 9 [])
        25 ((s 3).dropWhile isBit)) 24 (((s 3).takeWhile isBit).reverse) := by
  funext j
  by_cases scratch : j = 9 <;> by_cases suffix : j = 25 <;> by_cases scanned : j = 24 <;>
    simp [bitPrefix, Routine.seq, Routine.clear, Routine.assign_eval, Routine.transferWhile,
      scratch, suffix, scanned]

theorem bitPrefix_empty_iff (word : List Symbol) : word.dropWhile isBit = [] ↔ Binary word := by
  induction word with
  | nil => simp [Binary]
  | cons head rest ih => cases head <;> simp [isBit, Binary, ih]

theorem certificateCheck_result {O : Type} (s : Store) :
    (certificateCheck (O := O)).eval s 27 =
      if (s 3).length = (s 10).length ∧ Binary (s 3) then [.one] else [] := by
  have prefixFlag : ((s 3).dropWhile isBit).head?.isSome = decide (¬ Binary (s 3)) := by
    by_cases good : Binary (s 3)
    · simp [(bitPrefix_empty_iff _).mpr good, good]
    · have nonempty : (s 3).dropWhile isBit ≠ [] := by simpa [bitPrefix_empty_iff] using good
      cases word : (s 3).dropWhile isBit with
      | nil => exact False.elim (nonempty word)
      | cons head rest => simp [good]
  simp [certificateCheck, Routine.seq, LengthTest.routine_eval, certificateSlots,
    bitPrefix_eval, Routine.ofLocal, LengthTest.finish_eval]
  split_ifs <;> simp_all

theorem certificateCheck_frame {O : Type} (s : Store) (j : Fin 32)
    (scratch : j ≠ 9) (copy : j ≠ 22) (counter : j ≠ 23) (scanned : j ≠ 24)
    (suffix : j ≠ 25) (result : j ≠ 27) :
    (certificateCheck (O := O)).eval s j = s j := by
  simp [certificateCheck, Routine.seq, LengthTest.routine_eval, certificateSlots,
    bitPrefix_eval, Routine.ofLocal, LengthTest.finish_eval,
    scratch, copy, counter, scanned, suffix, result]

@[simp] theorem certificateCheck_randomFree {O : Type} : Command.RandomFree (certificateCheck (O := O)).command := by
  simp [certificateCheck, bitPrefix, LengthTest.routine, LengthTest.setup, DrainPair.routine]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeAssignment
