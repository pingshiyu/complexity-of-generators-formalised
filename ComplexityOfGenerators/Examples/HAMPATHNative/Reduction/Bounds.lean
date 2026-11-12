import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.DispatchBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Views
import ComplexityOfGenerators.Examples.HAMPATHNative.Syntax

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem routine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((routine (O := O)).eval s) (1000 * (budget + 3)) ∧
      (routine (O := O)).cost s ≤ 40000000 * (budget + 3)^2 := by
  let a := (prepareInput (O := O)).eval s
  let b := (parser (O := O)).eval a
  let c := (save (O := O)).eval b
  obtain ⟨aBound, aCost⟩ := prepareInput_bound (O := O) s budget sizes
  have bBound : StoreBound b (budget + 1) := parser_bound a budget aBound
  have parsedCost := parser_cost (O := O) a budget aBound
  obtain ⟨cBound, cCost⟩ := save_bound (O := O) b (budget + 1) (by omega) bBound
  obtain ⟨dBound, dCost⟩ := dispatch_bound (O := O) c (budget + 1) cBound
  refine ⟨dBound, ?_⟩
  change (prepareInput (O := O)).cost s + 1 +
    ((parser (O := O)).cost a + 1 + ((save (O := O)).cost b + 1 + (dispatch (O := O)).cost c)) ≤ _
  nlinarith only [aCost, parsedCost, cCost, dCost]

theorem singleton_randomFree {O : Type} : Command.RandomFree (singleton (O := O)).command := by
  simp only [singleton, Routine.randomFree_branch]
  intro label
  split <;> simp

theorem chooseSize_randomFree {O : Type} : Command.RandomFree (chooseSize (O := O)).command := by
  have choice : Command.RandomFree
      (Routine.branch (S := Symbol) (O := O) (21 : Fin 32) fun size => if size.isSome then large else singleton).command := by
    simp only [Routine.randomFree_branch]
    intro size
    split
    · exact large_randomFree
    · exact singleton_randomFree
  simp only [chooseSize, Routine.randomFree_seq]
  exact ⟨Routine.randomFree_assign _ _ _ _ _ _ _, Routine.randomFree_ofLocal _, choice⟩

theorem routine_randomFree {O : Type} : Command.RandomFree (routine (O := O)).command := by
  have inputPure : Command.RandomFree (prepareInput (O := O)).command := by simp [prepareInput]
  have savePure : Command.RandomFree (save (O := O)).command := by simp [save, metadata_randomFree]
  have dispatchPure : Command.RandomFree (dispatch (O := O)).command :=
    Routine.guardedOutput_randomFree 16 31 _ chooseSize_randomFree
  exact .seq inputPure (.seq parser_randomFree (.seq savePure dispatchPure))

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
