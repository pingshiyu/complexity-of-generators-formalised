import ComplexityOfGenerators.Examples.HAMPATHNative.Delete.MatrixBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Delete

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem finish_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((finish (O := O)).eval s) (4 * (budget + 1)) ∧
      (finish (O := O)).cost s ≤ 200 * (budget + 2) := by
  let a := (Routine.ofLocal (O := O) (Local.push (29 : Fin 32) Symbol.separator)).eval s
  let b := (contractPrepare (O := O)).eval a
  let c := (OneHot.routine (O := O) markSlots Symbol.bit).eval b
  have aBound : StoreBound a (budget + 1) :=
    (sizes.mono (by omega : budget ≤ budget + 1)).update 29 _ (by
      change (Symbol.separator :: s 29).length ≤ budget + 1
      simp only [List.length_cons]
      have length := sizes 29
      omega)
  obtain ⟨bBound, bCost⟩ := contractPrepare_bound (O := O) a (budget + 1) (by omega) aBound
  change StoreBound b (budget + 1) at bBound
  have clock := bBound 5
  have output := bBound 29
  have flag := bBound 8
  have cBound : StoreBound c (2 * (budget + 1)) :=
    OneHot.routine_bound markSlots Symbol.bit b (2 * (budget + 1))
      (bBound.mono (by omega)) (by omega) (by change (b 5).length + (b 29).length ≤ _; omega)
  have cCost := OneHot.routine_cost (O := O) markSlots Symbol.bit b
  change (OneHot.routine (O := O) markSlots Symbol.bit).cost b ≤ 11 * (b 5).length + 3 * (b 8).length + 3 at cCost
  have source := cBound 29
  have target := cBound 31
  constructor
  · change StoreBound ((Routine.transfer (O := O) 29 31 (by decide) id).eval c) _
    apply ((cBound.mono (by omega : 2 * (budget + 1) ≤ 4 * (budget + 1))).clear 29).update 31
    simp only [List.length_append, List.length_map, List.length_reverse]
    omega
  · change 1 + 1 + ((contractPrepare (O := O)).cost a + 1 +
      ((OneHot.routine (O := O) markSlots Symbol.bit).cost b + 1 + 6 * (c 29).length)) ≤ _
    omega

theorem routine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((routine (O := O)).eval s) (8 * (budget + 3)) ∧
      (routine (O := O)).cost s ≤ 2000 * (budget + 4)^2 := by
  let a := (headerPrefix (O := O)).eval s
  let b := (MatrixErase.rows (O := O)).eval ((matrixPrepare (O := O)).eval a)
  obtain ⟨aBound, aCost⟩ := headerPrefix_bound (O := O) s budget sizes
  obtain ⟨bBound, bCost⟩ := matrixPair_bound (O := O) a (budget + 1) aBound
  obtain ⟨finalBound, finalCost⟩ := finish_bound (O := O) b (2 * (budget + 1) + 3) bBound
  constructor
  · change StoreBound ((finish (O := O)).eval b) _
    exact finalBound.mono (by omega)
  · change (headerPrefix (O := O)).cost s + 1 +
      ((matrixPrepare (O := O)).cost a + 1 +
        ((MatrixErase.rows (O := O)).cost ((matrixPrepare (O := O)).eval a) + 1 + (finish (O := O)).cost b)) ≤ _
    nlinarith only [aCost, bCost, finalCost]

theorem contractPrepare_randomFree {O : Type} : Command.RandomFree (contractPrepare (O := O)).command := by
  have comparison : Command.RandomFree (RationalSelection.Compare.routine (O := O) nextSlots (Symbol.bit true)).command := by
    simp [RationalSelection.Compare.routine, RationalSelection.Compare.setup, DrainPair.routine]
  have choose : Command.RandomFree
      (Routine.branch (S := Symbol) (O := O) (20 : Fin 32) fun below => if below.isSome then Routine.skip else Routine.ofLocal (Local.pop 3)).command := by
    simp only [Routine.randomFree_branch]
    intro flag
    split <;> simp
  simp only [contractPrepare, Routine.randomFree_seq]
  exact ⟨Routine.randomFree_assign _ _ _ _ _ _ _, comparison, choose,
    Routine.randomFree_assign _ _ _ _ _ _ _, Routine.randomFree_ofLocal _⟩

theorem routine_randomFree {O : Type} : Command.RandomFree (routine (O := O)).command := by
  have initial : Command.RandomFree (headerPrefix (O := O)).command := by simp [headerPrefix]
  have prepared : Command.RandomFree (matrixPrepare (O := O)).command := by
    simp [matrixPrepare, header, headerExtract, headerSetup, headerClock, matrixSetup]
  have finished : Command.RandomFree (finish (O := O)).command := by
    simp [finish, contractPrepare_randomFree, OneHot.routine_randomFree]
  exact .seq initial (.seq prepared (.seq MatrixErase.rows_randomFree finished))

end ComplexityOfGenerators.Examples.HAMPATH.Native.Delete
