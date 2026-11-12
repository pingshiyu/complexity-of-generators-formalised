import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Productive
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.CounterRandomFree

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Productive

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem prepare_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (prepare.eval s) budget ∧ prepare.cost s ≤ 120*(budget+1) := by
  have first := Routine.clearMany_cost (O := Symbol) ([0,1,2,3,4,5,6,7,8,9,10,11] : List (Fin 16)) s budget (fun j _ => sizes j)
  let a := (Routine.clearMany (O := Symbol) ([0,1,2,3,4,5,6,7,8,9,10,11] : List (Fin 16))).eval s
  let b := (Routine.assign (O := Symbol) 12 0 13 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval a
  have aBound : StoreBound a budget := sizes.clearMany _
  have bBound : StoreBound b budget := aBound.assign _ _ _ _ _ _ _
  refine ⟨?_, ?_⟩
  · exact bBound.assign 12 1 13 (by decide) (by decide) (by decide) (fun _ => .bit true)
  · have a0 := aBound 0; have a12 := aBound 12; have a13 := aBound 13
    have b1 := bBound 1; have b12 := bBound 12; have b13 := bBound 13
    change (Routine.clearMany (O := Symbol) ([0,1,2,3,4,5,6,7,8,9,10,11] : List (Fin 16))).cost s+1+
      ((Routine.assign (O := Symbol) 12 0 13 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost a+1+
        (Routine.assign (O := Symbol) 12 1 13 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost b) ≤ _
    simp only [Routine.assign_cost, List.length_cons, List.length_nil] at *
    omega

theorem routine_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (routine.eval s) (max budget (BaseSearch.storeBudget (s 12).length)) ∧
      routine.cost s ≤ 120*(budget+1)+1+(s 12).length*(BaseSearch.bodyBudget (s 12).length+4) := by
  let n := (s 12).length
  have nativeBound : StoreBound (BaseSearch.search.eval (BaseSearch.initialStore n)) (BaseSearch.storeBudget n) := by
    simpa [StoreBound, BaseSearch.search, Routine.iterate, BaseSearch.initialStore, BaseSearch.counted] using
      BaseSearch.iterate_store_bound n n le_rfl
  have ambientBound := (prepare_bound s budget sizes).1
  refine ⟨?_, ?_⟩
  · intro j
    rw [routine_eval]
    by_cases low : j.val < 12
    · let i : Fin 12 := ⟨j.val, low⟩
      have same : slots i = j := Fin.ext rfl
      rw [← same, resultStore, Memory.patchStore_here]
      simp only [Local.mapStore, List.length_map]
      exact (nativeBound i).trans (le_max_right _ _)
    · have outside : ∀ i, j ≠ slots i := by
        intro i equality
        have same := congrArg (fun value : Fin 16 => value.val) equality
        change j.val = i.val at same
        have := i.isLt
        omega
      rw [resultStore, Memory.patchStore_outside slots _ _ j outside]
      have equality : preparedStore s = prepare.eval s := (prepare_eval s).symm
      rw [equality]
      exact (ambientBound j).trans (le_max_left _ _)
  · rw [routine_cost]
    have first := (prepare_bound s budget sizes).2
    have second := BaseSearch.search_cost n
    dsimp only [n] at second
    omega

theorem routine_randomFree : Command.RandomFree routine.command := by
  have source : Command.RandomFree BaseSearch.search.command := by
    simp [BaseSearch.search, BaseSearch.body, BaseSearch.remember, CounterRoutine.routine, CounterRoutine.setup, LengthTest.routine, LengthTest.setup, DrainPair.routine]
  unfold routine
  exact .seq (by simp [prepare]) ((source.mapSymbols (fun (_ : Unit) => Symbol.bit true) (fun _ => ())).rename slots)

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Productive
