import ComplexityOfGenerators.Examples.HAMPATHNative.Delete.Components
import ComplexityOfGenerators.Examples.HAMPATHNative.StateBounds
import ComplexityOfGenerators.Simulation.WordStack.ComparisonBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Delete

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem headerPrefix_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((headerPrefix (O := O)).eval s) (budget + 1) ∧
      (headerPrefix (O := O)).cost s ≤ 30 * (budget + 1) := by
  constructor
  · rw [headerPrefix_eval]
    apply (((sizes.mono (by omega : budget ≤ budget + 1)).clear 31).clear 9).update 29
    simp only [prefixWord, List.length_cons, List.length_replicate]
    have size := sizes 27
    omega
  · let a := (Routine.clear (O := O) 31).eval s
    have aBound : StoreBound a budget := sizes.clear 31
    have copying : (Routine.assign (O := O) 27 29 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost a ≤
        20 * budget + 3 := by
      rw [Routine.assign_cost]
      have := aBound 29
      have := aBound 9
      have := aBound 27
      omega
    have clearing := sizes 31
    change 3 * (s 31).length + 1 +
      ((Routine.assign (O := O) 27 29 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost a + 1 + (1 + 1 + 1)) ≤ _
    omega

theorem matrixSetup_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((matrixSetup (O := O)).eval s) budget ∧ (matrixSetup (O := O)).cost s ≤ 100 * (budget + 1) := by
  let a := (Routine.clearMany (O := O) [3, 9, 10, 13, 30, 31]).eval s
  let b := (Routine.assign (O := O) 4 27 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval a
  let c := (Routine.assign (O := O) 26 7 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval b
  let d := (Routine.assign (O := O) 7 26 9 (by decide) (by decide) (by decide) id).eval c
  have aBound : StoreBound a budget := sizes.clearMany _
  have bBound : StoreBound b budget := aBound.assign 4 27 9 (by decide) (by decide) (by decide) _
  have cBound : StoreBound c budget := bBound.assign 26 7 9 (by decide) (by decide) (by decide) _
  have dBound : StoreBound d budget := cBound.assign 7 26 9 (by decide) (by decide) (by decide) id
  have empty : d 13 = [] := by simp [d, c, b, a, Routine.assign_eval, Routine.clearMany_eval]
  unfold matrixSetup
  constructor
  · exact dBound.update 13 _ (by simpa [empty, Action.apply] using positive)
  · have clearing := Routine.clearMany_cost (O := O) ([3, 9, 10, 13, 30, 31] : List (Fin 32)) s budget
      (by intro j _; exact sizes j)
    have first : (Routine.assign (O := O) 4 27 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost a ≤
        20 * budget + 3 := by rw [Routine.assign_cost]; have := aBound 27; have := aBound 9; have := aBound 4; omega
    have second : (Routine.assign (O := O) 26 7 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost b ≤
        20 * budget + 3 := by rw [Routine.assign_cost]; have := bBound 7; have := bBound 9; have := bBound 26; omega
    have third : (Routine.assign (O := O) 7 26 9 (by decide) (by decide) (by decide) id).cost c ≤
        20 * budget + 3 := by rw [Routine.assign_cost]; have := cBound 26; have := cBound 9; have := cBound 7; omega
    simp only [List.length_cons, List.length_nil] at clearing
    change (Routine.clearMany (O := O) [3, 9, 10, 13, 30, 31]).cost s + 1 +
      ((Routine.assign (O := O) 4 27 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost a + 1 +
        ((Routine.assign (O := O) 26 7 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost b + 1 +
          ((Routine.assign (O := O) 7 26 9 (by decide) (by decide) (by decide) id).cost c + 1 + 1))) ≤ _
    omega

theorem matrixPrepare_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((matrixPrepare (O := O)).eval s) (budget + 1) ∧
      (matrixPrepare (O := O)).cost s ≤ 200 * (budget + 2) := by
  let a := (Routine.assign (O := O) 24 2 9 (by decide) (by decide) (by decide) id).eval s
  let b := (header (O := O)).eval a
  have aBound : StoreBound a budget := sizes.assign 24 2 9 (by decide) (by decide) (by decide) id
  have bBound : StoreBound b (budget + 1) := header_bound a budget aBound
  obtain ⟨finalBound, finalCost⟩ := matrixSetup_bound (O := O) b (budget + 1) (by omega) bBound
  have first : (Routine.assign (O := O) 24 2 9 (by decide) (by decide) (by decide) id).cost s ≤ 20 * budget + 3 := by
    rw [Routine.assign_cost]; have := sizes 2; have := sizes 9; have := sizes 24; omega
  have parsed := header_cost (O := O) a budget aBound
  unfold matrixPrepare
  exact ⟨finalBound, by change (Routine.assign (O := O) 24 2 9 (by decide) (by decide) (by decide) id).cost s + 1 +
    ((header (O := O)).cost a + 1 + (matrixSetup (O := O)).cost b) ≤ _; omega⟩

theorem contractPrepare_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((contractPrepare (O := O)).eval s) budget ∧
      (contractPrepare (O := O)).cost s ≤ 150 * (budget + 1) := by
  let a := (Routine.assign (O := O) 28 3 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval s
  let b := (RationalSelection.Compare.routine (O := O) nextSlots (.bit true)).eval a
  let choose : Routine Symbol O 32 := Routine.branch 20 fun below => if below.isSome then Routine.skip else Routine.ofLocal (Local.pop 3)
  let c := choose.eval b
  let d := (Routine.assign (O := O) 27 5 9 (by decide) (by decide) (by decide) id).eval c
  have aBound : StoreBound a budget := sizes.assign 28 3 9 (by decide) (by decide) (by decide) _
  have bBound : StoreBound b budget := aBound.strictCompare nextSlots (.bit true) positive
  have cBound : StoreBound c budget := by
    dsimp only [c, choose, Routine.branch]
    split
    · exact bBound
    · apply bBound.update 3
      change (b 3).tail.length ≤ budget
      have h := bBound 3
      simp only [List.length_tail]
      omega
  have dBound : StoreBound d budget := cBound.assign 27 5 9 (by decide) (by decide) (by decide) id
  unfold contractPrepare
  constructor
  · apply dBound.update 5
    change (d 5).tail.length ≤ budget
    have h := dBound 5
    simp only [List.length_tail]
    omega
  · have first : (Routine.assign (O := O) 28 3 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost s ≤
        20 * budget + 3 := by rw [Routine.assign_cost]; have := sizes 3; have := sizes 9; have := sizes 28; omega
    have comparison := RationalSelection.Compare.routine_cost (O := O) nextSlots (.bit true) a budget aBound
    have choosing : choose.cost b ≤ 2 := by
      dsimp only [choose, Routine.branch]
      split <;> simp [Routine.skip, Routine.ofLocal, Local.ticks, Local.pop]
    have last : (Routine.assign (O := O) 27 5 9 (by decide) (by decide) (by decide) id).cost c ≤
        20 * budget + 3 := by rw [Routine.assign_cost]; have := cBound 5; have := cBound 9; have := cBound 27; omega
    change (Routine.assign (O := O) 28 3 9 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost s + 1 +
      ((RationalSelection.Compare.routine (O := O) nextSlots (.bit true)).cost a + 1 +
        (choose.cost b + 1 + ((Routine.assign (O := O) 27 5 9 (by decide) (by decide) (by decide) id).cost c + 1 + 1))) ≤ _
    omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Delete
