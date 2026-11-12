import ComplexityOfGenerators.Examples.HAMPATHBaseGenerator
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Productive

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 16

def slots : Fin 12 ↪ Fin 16 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b same := Fin.ext (congrArg (fun j : Fin 16 => j.val) same)

def prepare : Routine Symbol Symbol 16 :=
  (Routine.clearMany [0,1,2,3,4,5,6,7,8,9,10,11]).seq
    ((Routine.assign 12 0 13 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      (Routine.assign 12 1 13 (by decide) (by decide) (by decide) (fun _ => .bit true)))

def preparedStore (s : Store) : Store :=
  fun j => if j.val < 12 then
    if j = 0 ∨ j = 1 then List.replicate (s 12).length (.bit true) else []
    else if j = 13 then [] else s j

theorem prepare_eval (s : Store) : prepare.eval s = preparedStore s := by
  funext j
  fin_cases j <;> simp [prepare, preparedStore, Routine.seq, Routine.clearMany_eval,
    Routine.assign_eval, List.map_const']

noncomputable def resultStore (s : Store) : Store :=
  Memory.patchStore slots
    (Local.mapStore (fun (_ : Unit) => Symbol.bit true)
      (BaseSearch.search.eval (BaseSearch.initialStore (s 12).length))) (preparedStore s)

noncomputable def routine : Routine Symbol Symbol 16 where
  command := prepare.command.seq
    (BaseSearch.search.embeddedCommand slots (fun (_ : Unit) => Symbol.bit true) (fun _ => ()))
  eval := resultStore
  cost := fun s => prepare.cost s+1+BaseSearch.search.cost (BaseSearch.initialStore (s 12).length)
  runs bits memory index := by
    obtain ⟨first, firstCost, firstRun⟩ := prepare.runs bits memory index
    let after : Memory Symbol Symbol 16 := { memory with store := prepare.eval memory.store }
    have prepared : ∀ j, after.store (slots j) =
        (BaseSearch.initialStore (memory.store 12).length j).map (fun (_ : Unit) => Symbol.bit true) := by
      intro j
      fin_cases j <;> simp [after, prepare_eval, preparedStore, slots, BaseSearch.initialStore]
    obtain ⟨second, secondCost, secondRun⟩ :=
      BaseSearch.search.embedded_runs slots (fun (_ : Unit) => Symbol.bit true) (fun _ => ())
        (fun b => by cases b; rfl) bits after (BaseSearch.initialStore (memory.store 12).length) index prepared
    refine ⟨first+1+second, by omega, ?_⟩
    have sequence := Command.Runs.seq memory after _ _ first second _ firstRun secondRun
    simpa only [after, resultStore, prepare_eval] using sequence

attribute [irreducible] routine

theorem routine_eval (s : Store) : routine.eval s = resultStore s := by unfold routine; rfl

theorem routine_cost (s : Store) :
    routine.cost s = prepare.cost s+1+BaseSearch.search.cost (BaseSearch.initialStore (s 12).length) := by
  unfold routine
  rfl

theorem routine_found (s : Store) :
    (routine.eval s 11).head?.isSome = decide (BaseSearch.Productive (s 12).length) := by
  have owned := Memory.patchStore_here slots
    (Local.mapStore (fun (_ : Unit) => Symbol.bit true)
      (BaseSearch.search.eval (BaseSearch.initialStore (s 12).length))) (preparedStore s) 11
  change resultStore s 11 = _ at owned
  rw [routine_eval, owned]
  simp only [Local.mapStore, List.head?_map, Option.isSome_map]
  exact BaseSearch.search_found (s 12).length

theorem routine_frame (s : Store) (j : Fin 16) (outside : 12 ≤ j.val) (scratch : j ≠ 13) :
    routine.eval s j = s j := by
  rw [routine_eval, resultStore, Memory.patchStore_outside]
  · simp [preparedStore, not_lt.mpr outside, scratch]
  · intro i same
    have equal := congrArg Fin.val same
    change j.val = i.val at equal
    omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Productive
