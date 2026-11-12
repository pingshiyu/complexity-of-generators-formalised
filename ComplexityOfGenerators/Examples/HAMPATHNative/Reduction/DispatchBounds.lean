import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.BasicBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.LargeBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem chooseSize_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((chooseSize (O := O)).eval s) (1000 * (budget + 2)) ∧
      (chooseSize (O := O)).cost s ≤ 20000000 * (budget + 2)^2 := by
  let a := (Routine.assign (O := O) 27 21 18 (by decide) (by decide) (by decide) id).eval s
  let b := (Routine.ofLocal (O := O) (Local.pop (21 : Fin 32))).eval a
  let choice : Routine Symbol O 32 := Routine.branch 21 fun size => if size.isSome then large else singleton
  have aBound : StoreBound a budget := sizes.assign 27 21 18 (by decide) (by decide) (by decide) id
  have bBound : StoreBound b budget := aBound.update 21 _ (by
    change (a 21).tail.length ≤ budget
    simp only [List.length_tail]
    have size := aBound 21
    omega)
  have selected : StoreBound (choice.eval b) (1000 * (budget + 2)) ∧
      choice.cost b ≤ 1 + 10000000 * (budget + 2)^2 := by
    cases head : (b 21).head? with
    | none =>
        obtain ⟨smallBound, smallCost⟩ := singleton_bound (O := O) b budget bBound
        simp only [choice, Routine.branch, head, Option.isSome_none, Bool.false_eq_true, ite_false]
        exact ⟨smallBound.mono (by omega), by nlinarith only [smallCost]⟩
    | some value =>
        obtain ⟨largeBound, largeCost⟩ := large_bound (O := O) b budget bBound
        simp only [choice, Routine.branch, head, Option.isSome_some, ite_true]
        exact ⟨largeBound, by omega⟩
  have copying : (Routine.assign (O := O) 27 21 18 (by decide) (by decide) (by decide) id).cost s ≤ 20 * budget + 3 := by
    rw [Routine.assign_cost]
    have := sizes 21
    have := sizes 18
    have := sizes 27
    omega
  refine ⟨selected.1, ?_⟩
  change (Routine.assign (O := O) 27 21 18 (by decide) (by decide) (by decide) id).cost s + 1 +
    (1 + 1 + choice.cost b) ≤ _
  have cost := selected.2
  nlinarith only [copying, cost]

theorem dispatch_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((dispatch (O := O)).eval s) (1000 * (budget + 2)) ∧
      (dispatch (O := O)).cost s ≤ 30000000 * (budget + 2)^2 := by
  obtain ⟨bodyBound, bodyCost⟩ := chooseSize_bound (O := O) s budget sizes
  obtain ⟨finalBound, finalCost⟩ := Routine.guardedOutput_bound 16 31 (chooseSize (O := O)) s budget
    (1000 * (budget + 2)) (20000000 * (budget + 2)^2) sizes (by omega) bodyBound bodyCost
  exact ⟨finalBound, by change (dispatch (O := O)).cost s ≤ _ at finalCost; nlinarith only [finalCost]⟩

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
