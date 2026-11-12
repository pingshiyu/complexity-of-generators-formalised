import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare
import ComplexityOfGenerators.Foundations.FixedBitBlocks
import Mathlib.Tactic.FinCases

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Bool 16

def powerSlots : Compare.Layout 16 := ⟨![0, 3, 6, 7, 8, 9], by decide⟩
def denominatorSlots : Compare.Layout 16 := ⟨![0, 5, 12, 7, 8, 9], by decide⟩
def numeratorSlots : Compare.Layout 16 := ⟨![1, 5, 13, 7, 8, 9], by decide⟩

def doublePower {O : Type} : Routine Bool O 16 :=
  (Routine.assign 3 11 9 (by decide) (by decide) (by decide) id).seq
    ((Routine.copy 11 3 9 (by decide) (by decide) (by decide) id).seq
      (Routine.ofLocal (Local.push 4 true)))

def logBody {O : Type} : Routine Bool O 16 :=
  (Compare.routine powerSlots true).seq
    (Routine.branch 6 fun flag => if flag.isSome then doublePower else Routine.skip)

def logSetup {O : Type} : Routine Bool O 16 :=
  (Routine.clearMany [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]).seq
  ((Routine.ofLocal (Local.push 3 true)).seq
    (Routine.assign 0 10 9 (by decide) (by decide) (by decide) id))

theorem logSetup_initial {O : Type} (s : Store) :
    (logSetup (O := O)).eval s 0 = s 0 ∧
    (logSetup (O := O)).eval s 1 = s 1 ∧
    (logSetup (O := O)).eval s 2 = s 2 ∧
    (logSetup (O := O)).eval s 3 = [true] ∧
    (logSetup (O := O)).eval s 4 = [] ∧
    (logSetup (O := O)).eval s 10 = s 0 := by
  simp [logSetup, Routine.seq, Routine.clearMany_eval, Routine.ofLocal, Routine.assign_eval]

theorem logBody_frame {O : Type} (s : Store) (j : Fin 16) (input : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 10) :
    (logBody (O := O)).eval s j = s j := by
  rcases input with rfl | rfl | rfl | rfl <;>
    simp [logBody, Routine.seq, Routine.branch, Compare.routine_eval, powerSlots,
      doublePower, Routine.assign_eval, Routine.copy, Routine.ofLocal]
    <;> split <;> simp [Routine.skip, Routine.ofLocal]

theorem logBody_power {O : Type} (s : Store) :
    (logBody (O := O)).eval s 3 =
      if (s 3).length < (s 0).length then s 3 ++ s 3 else s 3 := by
  simp [logBody, Routine.seq, Routine.branch, Compare.routine_eval, powerSlots]
  split_ifs <;> simp [doublePower, Routine.seq, Routine.assign_eval, Routine.copy,
    Routine.ofLocal, Routine.skip] <;> omega

theorem logBody_bits {O : Type} (s : Store) :
    (logBody (O := O)).eval s 4 =
      if (s 3).length < (s 0).length then true :: s 4 else s 4 := by
  simp [logBody, Routine.seq, Routine.branch, Compare.routine_eval, powerSlots]
  split_ifs <;> simp [doublePower, Routine.seq, Routine.assign_eval, Routine.copy,
    Routine.ofLocal, Routine.skip] <;> omega

def logCounted {O : Type} : Routine Bool O 16 := Routine.counted 10 logBody

theorem logCounted_frame {O : Type} (s : Store) (j : Fin 16) (input : j = 0 ∨ j = 1 ∨ j = 2) :
    (logCounted (O := O)).eval s j = s j := by
  change (logBody (O := O)).eval (Function.update s 10 (s 10).tail) j = s j
  rw [logBody_frame _ j (by rcases input with rfl | rfl | rfl <;> simp)]
  rcases input with rfl | rfl | rfl <;> simp

theorem logCounted_power {O : Type} (s : Store) :
    (logCounted (O := O)).eval s 3 =
      if (s 3).length < (s 0).length then s 3 ++ s 3 else s 3 := by
  simp [logCounted, Routine.counted, Routine.seq, Routine.ofLocal, logBody_power]

theorem logCounted_bits {O : Type} (s : Store) :
    (logCounted (O := O)).eval s 4 =
      if (s 3).length < (s 0).length then true :: s 4 else s 4 := by
  simp [logCounted, Routine.counted, Routine.seq, Routine.ofLocal, logBody_bits]

theorem logIterate_input {O : Type} (s : Store) (steps : ℕ) (j : Fin 16)
    (input : j = 0 ∨ j = 1 ∨ j = 2) :
    ((logCounted (O := O)).eval^[steps] ((logSetup (O := O)).eval s)) j = s j := by
  induction steps with
  | zero =>
    rcases input with rfl | rfl | rfl <;> simp [logSetup_initial]
  | succ steps ih => rw [Function.iterate_succ_apply', logCounted_frame _ _ input, ih]

theorem logIterate_values {O : Type} (s : Store) (steps : ℕ) :
    let d := (s 0).length
    let b := min steps (Nat.clog 2 d)
    ((logCounted (O := O)).eval^[steps] ((logSetup (O := O)).eval s)) 3 = List.replicate (2 ^ b) true ∧
    ((logCounted (O := O)).eval^[steps] ((logSetup (O := O)).eval s)) 4 = List.replicate b true := by
  dsimp only
  induction steps with
  | zero => simp [logSetup_initial]
  | succ steps ih =>
    rw [Function.iterate_succ_apply', logCounted_power, logCounted_bits,
      ih.1, ih.2, logIterate_input s steps 0 (by simp)]
    simp only [List.length_replicate]
    by_cases below : steps < Nat.clog 2 (s 0).length
    · have old : min steps (Nat.clog 2 (s 0).length) = steps := Nat.min_eq_left (by omega)
      have next : min (steps + 1) (Nat.clog 2 (s 0).length) = steps + 1 := Nat.min_eq_left (by omega)
      have small : 2 ^ steps < (s 0).length := (Nat.lt_clog_iff_pow_lt (by decide)).mp below
      simp only [old, next, small, ite_true]
      constructor
      · rw [← List.replicate_add, Nat.pow_succ]
        congr 1
        omega
      · rfl
    · have old : min steps (Nat.clog 2 (s 0).length) = Nat.clog 2 (s 0).length := Nat.min_eq_right (by omega)
      have next : min (steps + 1) (Nat.clog 2 (s 0).length) = Nat.clog 2 (s 0).length := Nat.min_eq_right (by omega)
      have large : ¬ 2 ^ Nat.clog 2 (s 0).length < (s 0).length :=
        Nat.not_lt_of_ge (Nat.le_pow_clog (by decide) _)
      simp [old, next, large]

def logRoutine {O : Type} : Routine Bool O 16 :=
  logSetup.seq (Routine.iterate 10 logBody (fun s => logBody_frame s 10 (by simp)))

theorem logRoutine_values {O : Type} (s : Store) :
    (logRoutine (O := O)).eval s 3 = List.replicate (2 ^ Nat.clog 2 (s 0).length) true ∧
    (logRoutine (O := O)).eval s 4 = List.replicate (Nat.clog 2 (s 0).length) true := by
  have values := logIterate_values (O := O) s (s 0).length
  have bound : Nat.clog 2 (s 0).length ≤ (s 0).length :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))
  simpa [logRoutine, Routine.seq, Routine.iterate, (logSetup_initial s).2.2.2.2.2,
    logCounted, Nat.min_eq_right bound] using values

theorem logRoutine_input {O : Type} (s : Store) (j : Fin 16) (input : j = 0 ∨ j = 1 ∨ j = 2) :
    (logRoutine (O := O)).eval s j = s j := by
  have frame := logIterate_input (O := O) s (s 0).length j input
  simpa [logRoutine, Routine.seq, Routine.iterate,
    (logSetup_initial s).2.2.2.2.2, logCounted] using frame

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection
