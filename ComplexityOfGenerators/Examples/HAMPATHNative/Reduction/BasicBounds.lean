import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Components

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem prepareInput_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((prepareInput (O := O)).eval s) budget ∧ (prepareInput (O := O)).cost s ≤ 50 * (budget + 1) := by
  let a := (Routine.clearMany (O := O) [2, 24, 25, 29, 31]).eval s
  let b := (Routine.transfer (O := O) 0 2 (by decide) id).eval a
  let c := (Routine.copy (O := O) 2 24 23 (by decide) (by decide) (by decide) id).eval b
  let d := (Routine.transfer (O := O) 1 25 (by decide) id).eval c
  have aBound : StoreBound a budget := sizes.clearMany _
  have aEmpty : a 2 = [] := by simp [a, Routine.clearMany_eval]
  have bBound : StoreBound b budget := MatrixErase.transfer_empty_bound 0 2 (by decide) a budget aBound aEmpty
  have bEmpty : b 24 = [] := by simp [b, a, Routine.transfer, Routine.clearMany_eval]
  have cBound : StoreBound c budget := by
    apply (bBound.clear 23).update 24
    simpa [bEmpty] using bBound 2
  have cEmpty : c 25 = [] := by simp [c, b, a, Routine.copy, Routine.transfer, Routine.clearMany_eval]
  have dBound : StoreBound d budget := MatrixErase.transfer_empty_bound 1 25 (by decide) c budget cBound cEmpty
  constructor
  · exact dBound
  · have clearing := Routine.clearMany_cost (O := O) ([2, 24, 25, 29, 31] : List (Fin 32)) s budget
      (by intro j _; exact sizes j)
    have input := aBound 0
    have word := bBound 2
    have scratch := bBound 23
    have label := cBound 1
    simp only [List.length_cons, List.length_nil] at clearing
    change (Routine.clearMany (O := O) [2, 24, 25, 29, 31]).cost s + 1 +
      (6 * (a 0).length + 1 + ((3 * (b 23).length + 14 * (b 2).length + 2) + 1 + 6 * (c 1).length)) ≤ _
    omega

theorem save_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget) (sizes : StoreBound s budget) :
    StoreBound ((save (O := O)).eval s) budget ∧ (save (O := O)).cost s ≤ 100 * (budget + 1) := by
  let a := (metadata (O := O)).eval s
  let b := (Routine.assign (O := O) 13 26 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).eval a
  have aBound : StoreBound a budget := metadata_bound s budget positive sizes
  have bBound : StoreBound b budget := aBound.assign 13 26 18 (by decide) (by decide) (by decide) _
  constructor
  · exact bBound.assign 4 27 18 (by decide) (by decide) (by decide) _
  · have first := metadata_cost (O := O) s budget sizes
    have second : (Routine.assign (O := O) 13 26 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost a ≤
        20 * budget + 3 := by rw [Routine.assign_cost]; have := aBound 26; have := aBound 18; have := aBound 13; omega
    have third : (Routine.assign (O := O) 4 27 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost b ≤
        20 * budget + 3 := by rw [Routine.assign_cost]; have := bBound 27; have := bBound 18; have := bBound 4; omega
    change (metadata (O := O)).cost s + 1 +
      ((Routine.assign (O := O) 13 26 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost a + 1 +
        (Routine.assign (O := O) 4 27 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost b) ≤ _
    omega

theorem singleton_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((singleton (O := O)).eval s) budget ∧ (singleton (O := O)).cost s ≤ 30 * (budget + 1) := by
  cases head : (s 25).head? with
  | none =>
      simp only [singleton, Routine.branch, head, Option.isSome_none, Bool.false_eq_true, ite_false]
      constructor
      · exact sizes.assign 24 31 18 (by decide) (by decide) (by decide) id
      · rw [Routine.assign_cost]
        have := sizes 31
        have := sizes 18
        have := sizes 24
        omega
  | some value =>
      simp only [singleton, Routine.branch, head, Option.isSome_some, ite_true]
      exact ⟨sizes.clear 31, by change 1 + 3 * (s 31).length ≤ _; have := sizes 31; omega⟩

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
