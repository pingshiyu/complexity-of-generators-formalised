import ComplexityOfGenerators.Examples.HAMPATHNative.Cell
import ComplexityOfGenerators.Simulation.WordStack.LengthTest
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.LabelChecks

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def isBit : Symbol → Bool | .bit _ => true | .separator => false

theorem all_bits (word : List Symbol) : word.all isBit = (word.dropWhile isBit).isEmpty := by
  induction word with
  | nil => rfl
  | cons head rest ih => cases head <;> simp [isBit, ih]

def bits {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 25 21 23 (by decide) (by decide) (by decide) id).seq
    ((Routine.clear 22).seq
      ((Routine.transferWhile 21 22 (by decide) isBit id).seq
        (Routine.branch 21 fun rest => if rest.isSome then Routine.clear 16 else Routine.skip)))

theorem bits_eval {O : Type} (s : Store) :
    (bits (O := O)).eval s =
      Function.update (Function.update (Function.update (Function.update s 23 [])
        21 ((s 25).dropWhile isBit)) 22 (((s 25).takeWhile isBit).reverse))
        16 (if (s 25).all isBit then s 16 else []) := by
  have suffix : ((s 25).dropWhile isBit).head?.isSome = !((s 25).dropWhile isBit).isEmpty := by
    cases (s 25).dropWhile isBit <;> rfl
  simp only [bits, Routine.seq, Routine.assign_eval, Routine.clear, Routine.transferWhile, Routine.branch]
  funext j
  by_cases valid : j = 16 <;> by_cases copy : j = 21 <;> by_cases moved : j = 22 <;> by_cases scratch : j = 23 <;>
    simp [Function.update_apply, Routine.clear, Routine.skip, Routine.ofLocal,
      suffix, all_bits, valid, copy, moved, scratch] <;>
    (try split) <;> simp_all

def require {O : Type} (expected : Bool) : Routine Symbol O 32 :=
  Routine.branch 20 fun found => if found.isSome = expected then Routine.skip else Routine.clear 16

theorem require_eval {O : Type} (expected : Bool) (s : Store) :
    (require (O := O) expected).eval s =
      Function.update s 16 (if (s 20).head?.isSome = expected then s 16 else []) := by
  simp only [require, Routine.branch]
  split <;> simp [Routine.skip, Routine.ofLocal, Routine.clear, Function.update_eq_self]

def lengthSlots : LengthTest.Layout 32 := ⟨![25, 19, 20, 21, 22, 23], by decide⟩
def belowSlots : RationalSelection.Compare.Layout 32 := ⟨![27, 28, 20, 21, 22, 23], by decide⟩
def equalSlots : LengthTest.Layout 32 := ⟨![28, 26, 20, 21, 22, 23], by decide⟩

def lengthCheck {O : Type} : Routine Symbol O 32 :=
  (LengthTest.routine lengthSlots (.bit true)).seq (require true)
def belowCheck {O : Type} : Routine Symbol O 32 :=
  (RationalSelection.Compare.routine belowSlots (.bit true)).seq (require true)
def differentCheck {O : Type} : Routine Symbol O 32 :=
  (LengthTest.routine equalSlots (.bit true)).seq (require false)

def correct (s : Store) : Bool :=
  (s 25).all isBit && decide ((s 25).length = (s 19).length) &&
    decide ((s 28).length < (s 27).length) && decide ((s 28).length ≠ (s 26).length)

def routine {O : Type} : Routine Symbol O 32 :=
  bits.seq (lengthCheck.seq (belowCheck.seq differentCheck))

theorem bits_frame {O : Type} (s : Store) (j : Fin 32)
    (valid : j ≠ 16) (copy : j ≠ 21) (counter : j ≠ 22) (scratch : j ≠ 23) :
    (bits (O := O)).eval s j = s j := by simp [bits_eval, valid, copy, counter, scratch]

theorem lengthCheck_flag {O : Type} (s : Store) :
    (lengthCheck (O := O)).eval s 16 = if (s 25).length = (s 19).length then s 16 else [] := by
  by_cases good : (s 25).length = (s 19).length <;>
    simp [lengthCheck, Routine.seq, LengthTest.routine_eval, require_eval, lengthSlots, good]

theorem belowCheck_flag {O : Type} (s : Store) :
    (belowCheck (O := O)).eval s 16 = if (s 28).length < (s 27).length then s 16 else [] := by
  by_cases good : (s 28).length < (s 27).length <;>
    simp [belowCheck, Routine.seq, RationalSelection.Compare.routine_eval, require_eval, belowSlots, good]

theorem differentCheck_flag {O : Type} (s : Store) :
    (differentCheck (O := O)).eval s 16 = if (s 28).length ≠ (s 26).length then s 16 else [] := by
  by_cases good : (s 28).length = (s 26).length <;>
    simp [differentCheck, Routine.seq, LengthTest.routine_eval, require_eval, equalSlots, good]

theorem lengthCheck_frame {O : Type} (s : Store) (j : Fin 32)
    (valid : j ≠ 16) (flag : j ≠ 20) (copy : j ≠ 21) (counter : j ≠ 22) (scratch : j ≠ 23) :
    (lengthCheck (O := O)).eval s j = s j := by
  simp [lengthCheck, Routine.seq, LengthTest.routine_eval, require_eval, lengthSlots, valid, flag, copy, counter, scratch]

theorem belowCheck_frame {O : Type} (s : Store) (j : Fin 32)
    (valid : j ≠ 16) (flag : j ≠ 20) (copy : j ≠ 21) (counter : j ≠ 22) (scratch : j ≠ 23) :
    (belowCheck (O := O)).eval s j = s j := by
  simp [belowCheck, Routine.seq, RationalSelection.Compare.routine_eval, require_eval, belowSlots,
    valid, flag, copy, counter, scratch]

theorem differentCheck_frame {O : Type} (s : Store) (j : Fin 32)
    (valid : j ≠ 16) (flag : j ≠ 20) (copy : j ≠ 21) (counter : j ≠ 22) (scratch : j ≠ 23) :
    (differentCheck (O := O)).eval s j = s j := by
  simp [differentCheck, Routine.seq, LengthTest.routine_eval, require_eval, equalSlots, valid, flag, copy, counter, scratch]

attribute [irreducible] bits lengthCheck belowCheck differentCheck

def inputRegisters : Fin 5 → Fin 32 := ![25, 19, 27, 28, 26]

theorem routine_flag {O : Type} (s : Store) :
    (routine (O := O)).eval s 16 = if correct s then s 16 else [] := by
  let a := (bits (O := O)).eval s
  let b := (lengthCheck (O := O)).eval a
  let c := (belowCheck (O := O)).eval b
  have aInput (i : Fin 5) : a (inputRegisters i) = s (inputRegisters i) := by
    fin_cases i <;> exact bits_frame s _ (by decide) (by decide) (by decide) (by decide)
  have bInput (i : Fin 5) : b (inputRegisters i) = s (inputRegisters i) := by
    apply Eq.trans _ (aInput i)
    fin_cases i <;> exact lengthCheck_frame a _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have cInput (i : Fin 5) : c (inputRegisters i) = s (inputRegisters i) := by
    apply Eq.trans _ (bInput i)
    fin_cases i <;> exact belowCheck_frame b _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have aFlag : a 16 = if (s 25).all isBit then s 16 else [] := by simp [a, bits_eval]
  have bFlag : b 16 = if (s 25).length = (s 19).length then a 16 else [] := by
    have value := lengthCheck_flag (O := O) a
    rw [show a 25 = s 25 from aInput 0, show a 19 = s 19 from aInput 1] at value
    exact value
  have cFlag : c 16 = if (s 28).length < (s 27).length then b 16 else [] := by
    have value := belowCheck_flag (O := O) b
    rw [show b 28 = s 28 from bInput 3, show b 27 = s 27 from bInput 2] at value
    exact value
  change (differentCheck (O := O)).eval c 16 = _
  rw [differentCheck_flag, show c 28 = s 28 from cInput 3, show c 26 = s 26 from cInput 4,
    cFlag, bFlag, aFlag]
  split_ifs <;> simp_all [correct]
  all_goals first | omega | aesop

theorem routine_frame {O : Type} (s : Store) (j : Fin 32)
    (valid : j ≠ 16) (flag : j ≠ 20) (copy : j ≠ 21) (counter : j ≠ 22) (scratch : j ≠ 23) :
    (routine (O := O)).eval s j = s j := by
  simp only [routine, Routine.seq]
  rw [differentCheck_frame _ j valid flag copy counter scratch, belowCheck_frame _ j valid flag copy counter scratch,
    lengthCheck_frame _ j valid flag copy counter scratch, bits_frame _ j valid copy counter scratch]

end ComplexityOfGenerators.Examples.HAMPATH.Native.LabelChecks
