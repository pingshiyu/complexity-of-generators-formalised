import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.Bounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

/-- The matrix width and the remaining old-row count are fixed or decrease. -/
def Counters (n : ℕ) (s : Store) : Prop := (s 1).length ≤ n ∧ (s 7).length ≤ n

theorem counters_pop (n : ℕ) (s : Store) (clock : Fin 16) (which : clock = 6 ∨ clock = 7)
    (valid : Counters n s) : Counters n (Function.update s clock (s clock).tail) := by
  rcases which with rfl | rfl
  · simpa [Counters] using valid
  · simpa [Counters, List.length_tail] using And.intro valid.1 ((Nat.sub_le _ _).trans valid.2)

theorem rowRoutine_counters {O : Type} (n : ℕ) (s : Store) (valid : Counters n s) :
    Counters n ((rowRoutine (O := O)).eval s) := by
  simpa [Counters, rowRoutine_eval_store, rowOutput] using valid

theorem firstBody_counters {O : Type} (n : ℕ) (s : Store) (valid : Counters n s) :
    Counters n ((firstBody (O := O)).eval s) :=
  counters_pop n _ 7 (Or.inr rfl) (rowRoutine_counters n s valid)

theorem firstBody_bound {O : Type} (n : ℕ) (s : Store) (budget : ℕ)
    (valid : Counters n s) (sizes : StoreBound s budget) :
    StoreBound ((firstBody (O := O)).eval s) (budget+n+1) := by
  have bound := rowRoutine_bound (O := O) s budget n sizes valid.1
  change StoreBound (Function.update ((rowRoutine (O := O)).eval s) 7 (((rowRoutine (O := O)).eval s) 7).tail) _
  exact bound.update 7 _ (by simp only [List.length_tail]; exact (Nat.sub_le _ _).trans (bound 7))

theorem firstBody_cost {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (firstBody (O := O)).cost s ≤ 1002*(budget+1) := by
  have cost := rowRoutine_cost (O := O) s budget sizes
  change (rowRoutine (O := O)).cost s+1+1 ≤ _
  omega

def middleCap (n : ℕ) : ℕ := n+1+n*(n+1)
def finalCap (n : ℕ) : ℕ := 10*(n+2)^2

theorem firstRows_bound {O : Type} (s : Store) (n : ℕ) (valid : Counters n s)
    (clock : (s 6).length ≤ n) (sizes : StoreBound s (n+1)) :
    Counters n ((firstRows (O := O)).eval s) ∧
      StoreBound ((firstRows (O := O)).eval s) (middleCap n) ∧
      (firstRows (O := O)).cost s ≤ n*1006*(middleCap n+1) := by
  have pop := fun t good => counters_pop n t 6 (Or.inl rfl) good
  have preserve := fun t good => firstBody_counters (O := O) n t good
  have grow : ∀ t budget, 0 ≤ budget → Counters n t → StoreBound t budget →
      StoreBound ((firstBody (O := O)).eval t) (budget+(n+1)) := by
    intro t budget _ good bounded
    simpa [Nat.add_assoc] using firstBody_bound (O := O) n t budget good bounded
  have cost : ∀ t budget, 0 ≤ budget → Counters n t → StoreBound t budget →
      (firstBody (O := O)).cost t ≤ 1002*(budget+1) := fun t budget _ _ bounded => firstBody_cost t budget bounded
  have fits : n+1+(s 6).length*(n+1) ≤ middleCap n := by
    unfold middleCap
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ clock) _
  obtain ⟨good, bound⟩ := Routine.iterate_growing_bound 6 (firstBody (O := O)) (Counters n) 0 (n+1)
    pop preserve grow firstBody_clock s (n+1) (by omega) valid sizes
  have time := Routine.iterate_growing_cost 6 (firstBody (O := O)) (Counters n) 0 (n+1) 1002
    pop preserve grow cost firstBody_clock s (n+1) (middleCap n) (by omega) valid sizes fits
  refine ⟨good, bound.mono fits, ?_⟩
  exact time.trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (1006*(middleCap n+1)) clock)

theorem restRows_bound {O : Type} (s : Store) (n budget : ℕ) (valid : Counters n s)
    (sizes : StoreBound s budget) :
    StoreBound ((restRows (O := O)).eval s) (budget+n*(n+1)) ∧
      (restRows (O := O)).cost s ≤ n*1004*(budget+n*(n+1)+1) := by
  have pop := fun t good => counters_pop n t 7 (Or.inr rfl) good
  have preserve := fun t good => rowRoutine_counters (O := O) n t good
  have grow : ∀ t budget, 0 ≤ budget → Counters n t → StoreBound t budget →
      StoreBound ((rowRoutine (O := O)).eval t) (budget+(n+1)) := by
    intro t budget _ good bounded
    simpa [Nat.add_assoc] using rowRoutine_bound (O := O) t budget n bounded good.1
  have cost : ∀ t budget, 0 ≤ budget → Counters n t → StoreBound t budget →
      (rowRoutine (O := O)).cost t ≤ 1000*(budget+1) := fun t budget _ _ bounded => rowRoutine_cost t budget bounded
  have fits : budget+(s 7).length*(n+1) ≤ budget+n*(n+1) :=
    Nat.add_le_add_left (Nat.mul_le_mul_right _ valid.2) _
  obtain ⟨_, bound⟩ := Routine.iterate_growing_bound 7 (rowRoutine (O := O)) (Counters n) 0 (n+1)
    pop preserve grow (fun t => rowRoutine_clock t 7 (Or.inr rfl)) s budget (by omega) valid sizes
  have time := Routine.iterate_growing_cost 7 (rowRoutine (O := O)) (Counters n) 0 (n+1) 1000
    pop preserve grow cost (fun t => rowRoutine_clock t 7 (Or.inr rfl)) s budget (budget+n*(n+1)) (by omega) valid sizes fits
  refine ⟨bound.mono fits, ?_⟩
  exact time.trans (by simpa [Nat.mul_assoc] using Nat.mul_le_mul_right (1004*(budget+n*(n+1)+1)) valid.2)

theorem routine_bound {O : Type} (s : Store) (n : ℕ) (sizes : StoreBound s (n+1))
    (width : (s 1).length ≤ n) (position : (s 2).length ≤ n) :
    StoreBound ((routine (O := O)).eval s) (finalCap n) ∧
      (routine (O := O)).cost s ≤ 100000*(n+2)^4 := by
  let a := (setup (O := O)).eval s
  let b := (firstRows (O := O)).eval a
  let c := (insertRow (O := O)).eval b
  have aBound : StoreBound a (n+1) :=
    (sizes.assign 2 6 14 (by decide) (by decide) (by decide) id).assign 1 7 14 (by decide) (by decide) (by decide) id
  have aCounters : Counters n a := by simpa [a, setup, Routine.seq, Routine.assign_eval, Counters] using And.intro width width
  have aClock : (a 6).length ≤ n := by simpa [a, setup, Routine.seq, Routine.assign_eval] using position
  obtain ⟨bCounters, bBound, bCost⟩ := firstRows_bound (O := O) a n aCounters aClock aBound
  change Counters n b at bCounters
  change StoreBound b (middleCap n) at bBound
  have cCounters : Counters n c := by simpa [c, insertRow, Routine.transfer, Counters] using bCounters
  have cBound : StoreBound c (2*middleCap n) := by
    change StoreBound (Function.update (Function.update b 4 []) 5 ((b 4).reverse.map id ++ b 5)) _
    apply ((bBound.mono (by omega)).clear 4).update 5
    simp only [List.length_append, List.length_map, List.length_reverse]
    have := bBound 4; have := bBound 5; omega
  obtain ⟨endBound, endCost⟩ := restRows_bound (O := O) c n (2*middleCap n) cCounters cBound
  have ceiling : 2*middleCap n+n*(n+1) ≤ finalCap n := by unfold middleCap finalCap; nlinarith
  refine ⟨endBound.mono ceiling, ?_⟩
  have first : (setup (O := O)).cost s ≤ 50*(n+2) := by
    let d := (Routine.assign (O := O) 2 6 14 (by decide) (by decide) (by decide) id).eval s
    have dBound : StoreBound d (n+1) := sizes.assign _ _ _ _ _ _ _
    have firstArgs := sizes 6; have secondArgs := sizes 14; have thirdArgs := sizes 2
    have fourthArgs := dBound 7; have fifthArgs := dBound 14; have sixthArgs := dBound 1
    change (Routine.assign (O := O) 2 6 14 (by decide) (by decide) (by decide) id).cost s+1+
      (Routine.assign (O := O) 1 7 14 (by decide) (by decide) (by decide) id).cost d ≤ _
    simp only [Routine.assign_cost]
    omega
  have inserted : (insertRow (O := O)).cost b ≤ 6*middleCap n := Nat.mul_le_mul_left 6 (bBound 4)
  change (setup (O := O)).cost s+1+((firstRows (O := O)).cost a+1+
    ((insertRow (O := O)).cost b+1+(restRows (O := O)).cost c)) ≤ _
  unfold middleCap at bCost inserted endCost
  nlinarith only [first, bCost, inserted, endCost]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert
