import ComplexityOfGenerators.Examples.HAMPATHNative.Logarithm
import ComplexityOfGenerators.Examples.HAMPATHLabels
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.DecodeBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.LabelBits

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def input (s : Store) : Local.Store Bool 16 := fun j =>
  if j = 2 then (s 25).map readBit ++ List.replicate (s 19).length false
  else if j = 4 then List.replicate (s 19).length true else []

def prepare {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]).seq
    ((Routine.assign 19 2 18 (by decide) (by decide) (by decide) (fun _ => .bit false)).seq
      ((Routine.copy 25 2 18 (by decide) (by decide) (by decide) (fun letter => .bit (readBit letter))).seq
        (Routine.assign 19 4 18 (by decide) (by decide) (by decide) (fun _ => .bit true))))

def preparedStore (s : Store) : Store := fun j =>
  if j.val < 16 then
    if j = 2 then ((s 25).map readBit ++ List.replicate (s 19).length false).map Symbol.bit
    else if j = 4 then List.replicate (s 19).length (.bit true) else []
  else if j = 18 then [] else s j

theorem prepare_eval {O : Type} (s : Store) : (prepare (O := O)).eval s = preparedStore s := by
  funext j
  fin_cases j <;> simp [prepare, preparedStore, Routine.seq, Routine.clearMany_eval, Routine.assign_eval,
    Routine.copy, List.map_const', List.map_append, List.map_map, Function.comp_def]

theorem input_enough (s : Store) : (input s 4).length ≤ (input s 2).length := by simp [input]

noncomputable def bankStore {O : Type} (s : Store) : Store := Memory.patchStore Logarithm.slots
  (Local.mapStore Symbol.bit ((RationalSelection.decodeRoutine (O := O)).eval (input s))) (preparedStore s)

noncomputable def bankRoutine {O : Type} : Routine Symbol O 32 where
  command := (prepare (O := O)).command.seq
    ((RationalSelection.decodeRoutine (O := O)).embeddedCommand Logarithm.slots Symbol.bit readBit)
  eval := bankStore
  cost := fun s => (prepare (O := O)).cost s + 1 + (RationalSelection.decodeRoutine (O := O)).cost (input s)
  runs bits memory index := by
    obtain ⟨first, firstCost, firstRun⟩ := (prepare (O := O)).runs bits memory index
    let after : Memory Symbol O 32 := {memory with store := (prepare (O := O)).eval memory.store}
    have prepared : ∀ j, after.store (Logarithm.slots j) = (input memory.store j).map Symbol.bit := by
      intro j
      fin_cases j <;> simp [after, prepare_eval, preparedStore, Logarithm.slots, input]
    obtain ⟨second, secondCost, secondRun⟩ :=
      (RationalSelection.decodeRoutine (O := O)).embedded_runs Logarithm.slots Symbol.bit readBit
        (fun b => rfl) bits after (input memory.store) index prepared
    refine ⟨first + 1 + second, by omega, ?_⟩
    have sequence := Command.Runs.seq memory after _ _ first second _ firstRun secondRun
    simpa only [after, bankStore, prepare_eval] using sequence

attribute [irreducible] bankRoutine

theorem bankRoutine_eval {O : Type} (s : Store) : (bankRoutine (O := O)).eval s = bankStore (O := O) s := by
  unfold bankRoutine
  rfl

theorem bankRoutine_cost {O : Type} (s : Store) :
    (bankRoutine (O := O)).cost s = (prepare (O := O)).cost s + 1 +
      (RationalSelection.decodeRoutine (O := O)).cost (input s) := by
  unfold bankRoutine
  rfl

theorem bankRoutine_owned {O : Type} (s : Store) (j : Fin 16) :
    (bankRoutine (O := O)).eval s (Logarithm.slots j) =
      ((RationalSelection.decodeRoutine (O := O)).eval (input s) j).map Symbol.bit := by
  rw [bankRoutine_eval]
  exact Memory.patchStore_here Logarithm.slots _ _ j

theorem bankRoutine_frame {O : Type} (s : Store) (j : Fin 32) (outside : 16 ≤ j.val) (scratch : j ≠ 18) :
    (bankRoutine (O := O)).eval s j = s j := by
  rw [bankRoutine_eval, bankStore, Memory.patchStore_outside]
  · simp [preparedStore, not_lt.mpr outside, scratch]
  · intro i same
    have equal := congrArg Fin.val same
    change j.val = i.val at equal
    have := i.isLt
    omega

noncomputable def routine {O : Type} : Routine Symbol O 32 :=
  bankRoutine.seq (Routine.assign 5 28 18 (by decide) (by decide) (by decide) id)

theorem routine_value {O : Type} (s : Store) :
    (routine (O := O)).eval s 28 =
      List.replicate (FixedBitBlocks.decode (((s 25).map readBit ++
        List.replicate (s 19).length false).take (s 19).length)) (.bit true) := by
  have fifth := bankRoutine_owned (O := O) s 5
  have value := (RationalSelection.decodeRoutine_values (O := O) (input s) (input_enough s)).2.1
  change (bankRoutine (O := O)).eval s 5 = _ at fifth
  simp only [routine, Routine.seq, Routine.assign_eval, Function.update_self]
  rw [fifth, value]
  simp [input]

theorem routine_frame {O : Type} (s : Store) (j : Fin 32) (outside : 16 ≤ j.val)
    (scratch : j ≠ 18) (output : j ≠ 28) : (routine (O := O)).eval s j = s j := by
  simp only [routine, Routine.seq, Routine.assign_eval, Function.update_apply, scratch, output, ↓reduceIte]
  exact bankRoutine_frame s j outside scratch

theorem routine_decodes {O : Type} (s : Store) (label : List Symbol) (next : ℕ)
    (word : s 25 = label) (width : (s 19).length = label.length) (decoded : decodeBits label = some next) :
    (routine (O := O)).eval s 28 = List.replicate next (.bit true) := by
  obtain ⟨bits, rfl, number⟩ := decodeBits_sound label next decoded
  rw [routine_value, word, width]
  simpa [List.map_map, Function.comp_def, readBit, List.take_left] using
    congrArg (fun n => List.replicate n (Symbol.bit true)) number

end ComplexityOfGenerators.Examples.HAMPATH.Native.LabelBits
