import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Power

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection

set_option backward.isDefEq.respectTransparency false

def doubleWeight {O : Type} : Routine Bool O 16 :=
  (Routine.assign 3 11 9 (by decide) (by decide) (by decide) id).seq
    (Routine.copy 11 3 9 (by decide) (by decide) (by decide) id)

def decodeBody {O : Type} : Routine Bool O 16 :=
  (Routine.branch 2 fun bit =>
    if bit.getD false then Routine.copy 3 5 9 (by decide) (by decide) (by decide) id else Routine.skip).seq
  ((Routine.ofLocal (Local.pop 2)).seq doubleWeight)

def decodeSetup {O : Type} : Routine Bool O 16 :=
  (Routine.clear 3).seq ((Routine.clear 5).seq (Routine.ofLocal (Local.push 3 true)))

theorem decodeSetup_initial {O : Type} (s : Store) :
    (decodeSetup (O := O)).eval s 0 = s 0 ∧
    (decodeSetup (O := O)).eval s 1 = s 1 ∧
    (decodeSetup (O := O)).eval s 2 = s 2 ∧
    (decodeSetup (O := O)).eval s 3 = [true] ∧
    (decodeSetup (O := O)).eval s 4 = s 4 ∧
    (decodeSetup (O := O)).eval s 5 = [] := by
  simp [decodeSetup, Routine.seq, Routine.clear, Routine.ofLocal]

theorem decodeBody_frame {O : Type} (s : Store) (j : Fin 16) (input : j = 0 ∨ j = 1 ∨ j = 4) :
    (decodeBody (O := O)).eval s j = s j := by
  rcases input with rfl | rfl | rfl <;>
    simp [decodeBody, Routine.seq, Routine.branch, Routine.copy, doubleWeight,
      Routine.assign_eval, Routine.ofLocal] <;> split <;> simp [Routine.skip, Routine.ofLocal]

theorem decodeBody_power {O : Type} (s : Store) :
    (decodeBody (O := O)).eval s 3 = s 3 ++ s 3 := by
  simp [decodeBody, Routine.seq, Routine.branch, Routine.copy, doubleWeight,
    Routine.assign_eval, Routine.ofLocal]
  split <;> simp [Routine.skip, Routine.ofLocal]

theorem decodeBody_value {O : Type} (s : Store) :
    (decodeBody (O := O)).eval s 5 =
      if (s 2).headD false then s 3 ++ s 5 else s 5 := by
  simp [decodeBody, Routine.seq, Routine.branch, Routine.copy, doubleWeight,
    Routine.assign_eval, Routine.ofLocal]
  split <;> simp [Routine.skip, Routine.ofLocal]

theorem decodeBody_bits {O : Type} (s : Store) :
    (decodeBody (O := O)).eval s 2 = (s 2).tail := by
  simp [decodeBody, Routine.seq, Routine.branch, Routine.copy, doubleWeight,
    Routine.assign_eval, Routine.ofLocal]
  split <;> simp [Routine.skip, Routine.ofLocal]

def decodeCounted {O : Type} : Routine Bool O 16 := Routine.counted 4 decodeBody

theorem decodeCounted_power {O : Type} (s : Store) :
    (decodeCounted (O := O)).eval s 3 = s 3 ++ s 3 := by
  simp [decodeCounted, Routine.counted, Routine.seq, Routine.ofLocal, decodeBody_power]

theorem decodeCounted_value {O : Type} (s : Store) :
    (decodeCounted (O := O)).eval s 5 =
      if (s 2).headD false then s 3 ++ s 5 else s 5 := by
  simp [decodeCounted, Routine.counted, Routine.seq, Routine.ofLocal, decodeBody_value]

theorem decodeCounted_bits {O : Type} (s : Store) :
    (decodeCounted (O := O)).eval s 2 = (s 2).tail := by
  simp [decodeCounted, Routine.counted, Routine.seq, Routine.ofLocal, decodeBody_bits]

theorem decodeIterate_values {O : Type} (s : Store) (steps : ℕ) (enough : steps ≤ (s 2).length) :
    ((decodeCounted (O := O)).eval^[steps] ((decodeSetup (O := O)).eval s)) 3 = List.replicate (2 ^ steps) true ∧
    ((decodeCounted (O := O)).eval^[steps] ((decodeSetup (O := O)).eval s)) 5 =
      List.replicate (FixedBitBlocks.decode ((s 2).take steps)) true ∧
    ((decodeCounted (O := O)).eval^[steps] ((decodeSetup (O := O)).eval s)) 2 = (s 2).drop steps := by
  induction steps with
  | zero => simp [decodeSetup_initial, FixedBitBlocks.decode]
  | succ steps ih =>
    obtain ⟨power, value, bits⟩ := ih (by omega)
    have inside : steps < (s 2).length := by omega
    have head : ((s 2).drop steps).headD false = (s 2)[steps] := by
      simp [List.head?_eq_getElem?, List.getElem?_drop,
        List.getElem?_eq_getElem inside]
    have blockPrefix := FixedBitBlocks.decode_take_succ (s 2) steps inside
    rw [Function.iterate_succ_apply', decodeCounted_power, decodeCounted_value, decodeCounted_bits,
      power, value, bits, head]
    refine ⟨?_, ?_, List.tail_drop⟩
    · rw [← List.replicate_add, Nat.pow_succ]
      congr 1
      omega
    · cases letter : (s 2)[steps] with
      | false => simpa [letter] using congrArg (fun n => List.replicate n true) blockPrefix.symm
      | true =>
        rw [ite_eq_left (show true = true from rfl), ← List.replicate_add]
        congr 1
        simpa [letter, Nat.add_comm] using blockPrefix.symm

def decodeRoutine {O : Type} : Routine Bool O 16 :=
  decodeSetup.seq (Routine.iterate 4 decodeBody (fun s => decodeBody_frame s 4 (by simp)))

theorem decodeRoutine_values {O : Type} (s : Store) (enough : (s 4).length ≤ (s 2).length) :
    (decodeRoutine (O := O)).eval s 3 = List.replicate (2 ^ (s 4).length) true ∧
    (decodeRoutine (O := O)).eval s 5 = List.replicate (FixedBitBlocks.decode ((s 2).take (s 4).length)) true ∧
    (decodeRoutine (O := O)).eval s 2 = (s 2).drop (s 4).length := by
  have values := decodeIterate_values (O := O) s (s 4).length enough
  simpa [decodeRoutine, Routine.seq, Routine.iterate,
    (decodeSetup_initial s).2.2.2.2.1, decodeCounted] using values

theorem decodeRoutine_input {O : Type} (s : Store) (j : Fin 16) (input : j = 0 ∨ j = 1) :
    (decodeRoutine (O := O)).eval s j = s j := by
  have different : j ≠ 4 := by rcases input with rfl | rfl <;> decide
  have stable := Routine.iterate_frame 4 (decodeBody (O := O))
    (fun t => decodeBody_frame t 4 (by simp)) j different
    (fun t => decodeBody_frame t j (by rcases input with rfl | rfl <;> simp))
    ((decodeSetup (O := O)).eval s)
  have initial : (decodeSetup (O := O)).eval s j = s j := by
    rcases input with rfl | rfl
    · exact (decodeSetup_initial s).1
    · exact (decodeSetup_initial s).2.1
  exact stable.trans initial

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection
