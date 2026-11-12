import ComplexityOfGenerators.Examples.HAMPATHNative.Cell
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.PowerBounds
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Logarithm

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def slots : Fin 16 ↪ Fin 32 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b same := Fin.ext (congrArg (fun j : Fin 32 => j.val) same)

def input (s : Store) : Local.Store Bool 16 :=
  fun j => if j = 0 then List.replicate (s 17).length true else []

def prepare {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]).seq
    (Routine.assign 17 0 18 (by decide) (by decide) (by decide) (fun _ => .bit true))

def preparedStore (s : Store) : Store :=
  fun j => if j.val < 16 then
    if j = 0 then List.replicate (s 17).length (.bit true) else []
    else if j = 18 then [] else s j

theorem prepare_eval {O : Type} (s : Store) : (prepare (O := O)).eval s = preparedStore s := by
  funext j
  fin_cases j <;> simp [prepare, preparedStore, slots, input, Local.mapStore,
    Routine.seq, Routine.clearMany_eval, Routine.assign_eval, List.map_const']

noncomputable def bankStore {O : Type} (s : Store) : Store :=
  Memory.patchStore slots
    (Local.mapStore Symbol.bit ((RationalSelection.logRoutine (O := O)).eval (input s))) (preparedStore s)

noncomputable def bankRoutine {O : Type} : Routine Symbol O 32 where
  command := (prepare (O := O)).command.seq
    ((RationalSelection.logRoutine (O := O)).embeddedCommand slots Symbol.bit readBit)
  eval := bankStore
  cost := fun s => (prepare (O := O)).cost s + 1 + (RationalSelection.logRoutine (O := O)).cost (input s)
  runs bits memory index := by
    obtain ⟨first, firstCost, firstRun⟩ := (prepare (O := O)).runs bits memory index
    let after : Memory Symbol O 32 := {memory with store := (prepare (O := O)).eval memory.store}
    have prepared : ∀ j, after.store (slots j) = (input memory.store j).map Symbol.bit := by
      intro j
      fin_cases j <;> simp [after, prepare_eval, preparedStore, slots, input]
    obtain ⟨second, secondCost, secondRun⟩ :=
      (RationalSelection.logRoutine (O := O)).embedded_runs slots Symbol.bit readBit
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
      (RationalSelection.logRoutine (O := O)).cost (input s) := by
  unfold bankRoutine
  rfl

theorem bankRoutine_owned {O : Type} (s : Store) (j : Fin 16) :
    (bankRoutine (O := O)).eval s (slots j) =
      ((RationalSelection.logRoutine (O := O)).eval (input s) j).map Symbol.bit := by
  rw [bankRoutine_eval]
  exact Memory.patchStore_here slots _ _ j

theorem bankRoutine_frame {O : Type} (s : Store) (j : Fin 32) (outside : 16 ≤ j.val) (scratch : j ≠ 18) :
    (bankRoutine (O := O)).eval s j = s j := by
  rw [bankRoutine_eval, bankStore, Memory.patchStore_outside]
  · simp [preparedStore, not_lt.mpr outside, scratch]
  · intro i same
    have equal := congrArg Fin.val same
    change j.val = i.val at equal
    have := i.isLt
    omega

theorem bankRoutine_value {O : Type} (s : Store) :
    (bankRoutine (O := O)).eval s 4 = List.replicate (Nat.clog 2 (s 17).length) (.bit true) := by
  have fourth := bankRoutine_owned (O := O) s 4
  have value := (RationalSelection.logRoutine_values (O := O) (input s)).2
  change (bankRoutine (O := O)).eval s 4 = _ at fourth
  rw [fourth, value]
  simp [input]

noncomputable def routine {O : Type} : Routine Symbol O 32 :=
  bankRoutine.seq (Routine.assign 4 19 18 (by decide) (by decide) (by decide) id)

theorem routine_value {O : Type} (s : Store) :
    (routine (O := O)).eval s 19 = List.replicate (Nat.clog 2 (s 17).length) (.bit true) := by
  simp only [routine, Routine.seq, Routine.assign_eval, Function.update_self]
  rw [bankRoutine_value]
  simp

theorem routine_frame {O : Type} (s : Store) (j : Fin 32) (outside : 16 ≤ j.val)
    (scratch : j ≠ 18) (output : j ≠ 19) : (routine (O := O)).eval s j = s j := by
  simp only [routine, Routine.seq, Routine.assign_eval, Function.update_apply, scratch, output, ↓reduceIte]
  exact bankRoutine_frame s j outside scratch

end ComplexityOfGenerators.Examples.HAMPATH.Native.Logarithm
