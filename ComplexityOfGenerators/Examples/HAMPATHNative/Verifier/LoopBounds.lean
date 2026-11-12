import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.StepBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] body

theorem counted_bound (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n))
    (current : (s 32).length ≤ n) (remaining : (s 33).length ≤ n) :
    StoreBound ((Routine.counted 34 body).eval s) (workspace n) ∧
      (Routine.counted 34 body).cost s ≤ stepBudget n + 3 := by
  let a := (Routine.ofLocal (O := Unit) (Local.pop (34 : Fin 64))).eval s
  have aBound : StoreBound a (workspace n) := sizes.update 34 (s 34).tail (by simp only [List.length_tail]; have := sizes 34; omega)
  have aCurrent : (a 32).length ≤ n := by simpa [a, Routine.ofLocal, Local.eval_pop] using current
  have aRemaining : (a 33).length ≤ n := by simpa [a, Routine.ofLocal, Local.eval_pop] using remaining
  obtain ⟨bound, clock⟩ := body_bound a n aBound aCurrent aRemaining
  refine ⟨bound, ?_⟩
  change 1 + 1 + body.cost a ≤ _
  omega

theorem iterate_bound (count : ℕ) (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n))
    (current : (s 32).length ≤ n) (remaining : (s 33).length ≤ n) :
    StoreBound ((Routine.counted 34 body).eval^[count] s) (workspace n) := by
  induction count with
  | zero => exact sizes
  | succ count ih =>
      let a := (Routine.counted 34 body).eval^[count] s
      have semantic := iterate_view count s
      have aCurrent : (a 32).length ≤ n := by
        have bound := (iterate_current_length_le count (view s)).trans current
        change (view a).current.length ≤ n
        rw [semantic]
        exact bound
      have aRemaining : (a 33).length ≤ n := by
        have bound := (iterate_remaining_length_le count (view s)).trans remaining
        change (view a).remaining.length ≤ n
        rw [semantic]
        exact bound
      rw [Function.iterate_succ_apply']
      exact (counted_bound a n ih aCurrent aRemaining).1

theorem loop_bound (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n))
    (current : (s 32).length ≤ n) (remaining : (s 33).length ≤ n) (clock : (s 34).length ≤ n) :
    StoreBound (loop.eval s) (workspace n) ∧ loop.cost s ≤ n * (stepBudget n + 5) := by
  refine ⟨iterate_bound _ s n sizes current remaining, ?_⟩
  change Routine.loopCost (Routine.counted 34 body).cost (Routine.counted 34 body).eval (s 34).length s ≤ _
  apply (Routine.loopCost_bound _ _ _ (stepBudget n+3) s ?_).trans
    (Nat.mul_le_mul_right _ clock)
  intro i hi
  let a := (Routine.counted 34 body).eval^[i] s
  have aBound := iterate_bound i s n sizes current remaining
  have semantic := iterate_view i s
  have aCurrent : (a 32).length ≤ n := by
    change (view a).current.length ≤ n
    rw [semantic]
    exact (iterate_current_length_le i (view s)).trans current
  have aRemaining : (a 33).length ≤ n := by
    change (view a).remaining.length ≤ n
    rw [semantic]
    exact (iterate_remaining_length_le i (view s)).trans remaining
  exact (counted_bound a n aBound aCurrent aRemaining).2

theorem loop_randomFree : Command.RandomFree loop.command := Routine.randomFree_iterate 34 body body_clock body_randomFree

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
