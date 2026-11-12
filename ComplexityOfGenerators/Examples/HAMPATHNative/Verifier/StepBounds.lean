import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Components
import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.CallsBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] widthRoutine Reduction.routine

def workspace (n : ℕ) : ℕ := 1000 * (2*n + 3)

def stepBudget (n : ℕ) : ℕ := 500000000 * (n + 3)^2

theorem width_native_bound (word : List Symbol) (n : ℕ) (inside : word.length ≤ n) :
    StoreBound (widthRoutine.eval (Reduction.loadedStore word [])) (4*(n+2)) ∧
      widthRoutine.cost (Reduction.loadedStore word []) ≤ 2000*(n+2)^2 := by
  rw [width_loaded]
  let a := (prepared word ([] : List Unit)).store
  let b := (parser (O := Unit)).eval a
  let c := (metadata (O := Unit)).eval b
  let d := (Logarithm.routine (O := Unit)).eval c
  have aBound : StoreBound a n := by
    intro j
    exact (prepared_sizes word [] j).trans (by simpa using inside)
  have bBound : StoreBound b (n+1) := parser_bound a n aBound
  have cBound : StoreBound c (n+1) := metadata_bound b (n+1) (by omega) bBound
  have dBound : StoreBound d (4*(n+2)) := (Logarithm.routine_bound (O := Unit) c (n+1) cBound).1
  have endBound : StoreBound ((gate (O := Unit) 19).eval d) (4*(n+2)) := by
    simp only [gate, Routine.branch]
    split
    · exact dBound
    · exact dBound.clear 19
  have first : prepare.cost (loaded word ([] : List Unit)).store = 6*word.length := by simp [prepare, loaded, Routine.transfer]
  have middle := parser_cost (O := Unit) a n aBound
  have last := widthCore_cost (O := Unit) b (n+1) (by omega) bBound
  refine ⟨?_, ?_⟩
  · unfold widthRoutine widthCore
    exact endBound
  unfold widthRoutine
  change prepare.cost (loaded word ([] : List Unit)).store + 1 +
    ((parser (O := Unit)).cost a + 1 + (widthCore (O := Unit)).cost b) ≤ _
  rw [first]
  nlinarith only [inside, middle, last]

theorem widthCall_bound (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n))
    (current : (s 32).length ≤ n) :
    StoreBound (widthCall.eval s) (workspace n) ∧
      widthCall.cost s ≤ 2000*(n+2)^2 + 404*(workspace n+1) := by
  let a := (Routine.clear (O := Unit) 36).eval s
  have aBound : StoreBound a (workspace n) := sizes.clear 36
  have source := width_native_bound (s 32) n current
  have loadedEq : Reduction.loadedStore (a 32) (a 36) = Reduction.loadedStore (s 32) [] := by simp [a, Routine.clear]
  have cap : 4*(n+2) ≤ workspace n := by unfold workspace; omega
  obtain ⟨bound, clock⟩ := invoke_bound widthRoutine 19 39 (by decide) (by decide) a (workspace n) (2000*(n+2)^2)
    aBound (by rw [loadedEq]; exact source.1.mono cap) (by rw [loadedEq]; exact source.2)
  refine ⟨bound, ?_⟩
  change 3*(s 36).length + 1 + (invoke widthRoutine 19 39 (by decide) (by decide)).cost a ≤ _
  have := sizes 36
  omega

theorem splitLabel_bound (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n)) (empty : s 36 = []) :
    StoreBound (splitLabel.eval s) (workspace n) ∧ splitLabel.cost s ≤ 20*(workspace n+1) := by
  let a := (Routine.clear (O := Unit) 35).eval s
  let b := (Blocks.routine (O := Unit) 39 33 35 (by decide) (by decide)).eval a
  have aBound : StoreBound a (workspace n) := sizes.clear 35
  have bBound : StoreBound b (workspace n) := aBound.block 39 33 35 (by decide) (by decide) (by decide) (by simp [a, Routine.clear])
  have labelEmpty : b 36 = [] := by simp [b, a, Blocks.routine_eval (O := Unit) (39 : Fin 64) 33 35 (by decide) (by decide) (by decide), Routine.clear, empty]
  have finalBound := transfer_bound b (workspace n) bBound 35 36 (by decide) labelEmpty
  have blockCost := Blocks.routine_cost (O := Unit) (39 : Fin 64) 33 35 (by decide) (by decide) a
  have sourceClock : (a 39).length ≤ workspace n := aBound 39
  have transferCost : (Routine.transfer (O := Unit) 35 36 (by decide) id).cost b ≤ 6*workspace n := Nat.mul_le_mul_left 6 (bBound 35)
  refine ⟨finalBound, ?_⟩
  change 3*(s 35).length + 1 + ((Blocks.routine (O := Unit) 39 33 35 (by decide) (by decide)).cost a + 1 +
    (Routine.transfer (O := Unit) 35 36 (by decide) id).cost b) ≤ _
  have := sizes 35
  omega

theorem reduceCall_bound (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n))
    (current : (s 32).length ≤ n) (label : (s 36).length ≤ n) :
    StoreBound (reduceCall.eval s) (workspace n) ∧
      reduceCall.cost s ≤ 40000000*(2*n+3)^2 + 400*(workspace n+1) := by
  have loadedBound : StoreBound (Reduction.loadedStore (s 32) (s 36)) (2*n) :=
    (Reduction.loaded_bound (s 32) (s 36)).mono (by omega)
  obtain ⟨source, clock⟩ := Reduction.routine_bound (O := Unit) _ (2*n) loadedBound
  exact invoke_bound _ _ _ _ _ s (workspace n) _ sizes source clock

theorem activeStep_bound (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n))
    (current : (s 32).length ≤ n) (remaining : (s 33).length ≤ n) :
    StoreBound (activeStep.eval s) (workspace n) ∧ activeStep.cost s ≤ stepBudget n := by
  let a := widthCall.eval s
  let b := splitLabel.eval a
  obtain ⟨aBound, aCost⟩ := widthCall_bound s n sizes current
  obtain ⟨bBound, bCost⟩ := splitLabel_bound a n aBound (widthCall_label s)
  have fields := splitLabel_fields a (widthCall_label s)
  change b 32 = a 32 ∧ b 33 = (a 33).drop (a 39).length ∧ b 36 = (a 33).take (a 39).length ∧ b 34 = a 34 at fields
  have aCurrent : a 32 = s 32 := widthCall_frame s 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have aRemaining : a 33 = s 33 := widthCall_frame s 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have bCurrent : (b 32).length ≤ n := by rw [fields.1, aCurrent]; exact current
  have bLabel : (b 36).length ≤ n := by rw [fields.2.2.1, List.length_take, aRemaining]; exact (Nat.min_le_right _ _).trans remaining
  obtain ⟨endBound, endCost⟩ := reduceCall_bound b n bBound bCurrent bLabel
  refine ⟨endBound, ?_⟩
  change widthCall.cost s + 1 + (splitLabel.cost a + 1 + reduceCall.cost b) ≤ _
  unfold stepBudget
  unfold workspace at aCost bCost endCost
  nlinarith only [aCost, bCost, endCost]

theorem body_bound (s : Store) (n : ℕ) (sizes : StoreBound s (workspace n))
    (current : (s 32).length ≤ n) (remaining : (s 33).length ≤ n) :
    StoreBound (body.eval s) (workspace n) ∧ body.cost s ≤ stepBudget n + 1 := by
  simp only [body, Routine.branch]
  split
  · obtain ⟨bound, clock⟩ := activeStep_bound s n sizes current remaining
    exact ⟨bound, by omega⟩
  · exact ⟨sizes, by simp [Routine.skip, Routine.ofLocal, Local.ticks]⟩

theorem widthCall_randomFree : Command.RandomFree widthCall.command := by
  exact .seq (by simp) (invoke_randomFree _ _ _ _ _ widthRoutine_randomFree)

theorem splitLabel_randomFree : Command.RandomFree splitLabel.command := by simp [splitLabel, Blocks.routine, Blocks.body]

theorem body_randomFree : Command.RandomFree body.command := by
  have active : Command.RandomFree activeStep.command :=
    .seq widthCall_randomFree (.seq splitLabel_randomFree (invoke_randomFree _ _ _ _ _ Reduction.routine_randomFree))
  simp only [body, Routine.randomFree_branch]
  intro head
  split
  · exact active
  · simp

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
