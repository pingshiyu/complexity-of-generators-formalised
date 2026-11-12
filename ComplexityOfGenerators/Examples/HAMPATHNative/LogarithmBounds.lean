import ComplexityOfGenerators.Examples.HAMPATHNative.Logarithm
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Logarithm

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

variable {O : Type}

theorem input_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound (input s) budget := by
  intro j
  by_cases zero : j = 0
  · simpa [input, zero] using sizes 17
  · simp [input, zero]

theorem prepare_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((prepare (O := O)).eval s) budget := by
  exact (sizes.clearMany (O := O) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 32))).assign
    17 0 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)

theorem prepare_cost (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (prepare (O := O)).cost s ≤ 70 * (budget + 1) := by
  let cleared := (Routine.clearMany (S := Symbol) (O := O) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 32))).eval s
  have clearCost := Routine.clearMany_cost (O := O) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 32)) s budget
    (fun j _ => sizes j)
  have clearedSizes : StoreBound cleared budget := sizes.clearMany (O := O) _
  have source := clearedSizes 17
  have target := clearedSizes 0
  have scratch := clearedSizes 18
  have length : ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 32)).length = 16 := by simp
  rw [length] at clearCost
  change (Routine.clearMany (O := O) ([0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] : List (Fin 32))).cost s + 1 +
    (Routine.assign (O := O) 17 0 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost cleared ≤ _
  rw [Routine.assign_cost]
  omega

theorem bankRoutine_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((bankRoutine (O := O)).eval s) (4 * (budget + 1)) := by
  have prepared := prepare_bound (O := O) s budget sizes
  have localBound := RationalSelection.logRoutine_bound (O := O) (input s) budget (input_bound s budget sizes)
  intro j
  by_cases owned : j.val < 16
  · let privateIndex : Fin 16 := ⟨j.val, owned⟩
    have same : slots privateIndex = j := by apply Fin.ext; rfl
    rw [← same, bankRoutine_owned, List.length_map]
    exact localBound privateIndex
  · have outside : ∀ i : Fin 16, j ≠ slots i := by
      intro i same
      have equal := congrArg Fin.val same
      have := i.isLt
      change j.val = i.val at equal
      omega
    rw [bankRoutine_eval, bankStore, Memory.patchStore_outside slots _ _ j outside]
    have small : ((preparedStore s) j).length ≤ budget := by
      simpa only [prepare_eval] using prepared j
    omega

theorem bankRoutine_cost_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (bankRoutine (O := O)).cost s ≤ 700 * (budget + 1)^2 := by
  rw [bankRoutine_cost]
  have initial := prepare_cost (O := O) s budget sizes
  have loop := RationalSelection.logRoutine_cost (O := O) (input s) budget (input_bound s budget sizes)
  nlinarith

/-- The logarithm wrapper is total, keeps every store within a linear cap,
and uses a quadratic number of actual primitive commands. -/
theorem routine_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((routine (O := O)).eval s) (4 * (budget + 1)) ∧
      (routine (O := O)).cost s ≤ 1000 * (budget + 1)^2 := by
  have bankBound := bankRoutine_bound (O := O) s budget sizes
  constructor
  · exact bankBound.assign (O := O) 4 19 18 (by decide) (by decide) (by decide) id
  · have bankCost := bankRoutine_cost_bound (O := O) s budget sizes
    have source := bankBound 4
    have target := bankBound 19
    have scratch := bankBound 18
    change (bankRoutine (O := O)).cost s + 1 +
      (Routine.assign (O := O) 4 19 18 (by decide) (by decide) (by decide) id).cost ((bankRoutine (O := O)).eval s) ≤ _
    rw [Routine.assign_cost]
    nlinarith

theorem logRoutine_randomFree : Command.RandomFree (RationalSelection.logRoutine (O := O)).command := by
  have comparison : Command.RandomFree (RationalSelection.Compare.routine (O := O) RationalSelection.powerSlots true).command := by
    simp [RationalSelection.Compare.routine, RationalSelection.Compare.setup, DrainPair.routine]
  have double : Command.RandomFree (RationalSelection.doublePower (O := O)).command := by
    simp [RationalSelection.doublePower]
  have body : Command.RandomFree (RationalSelection.logBody (O := O)).command := by
    rw [RationalSelection.logBody, Routine.randomFree_seq]
    refine ⟨comparison, ?_⟩
    apply (Routine.randomFree_branch _ _).mpr
    intro flag
    split_ifs
    · exact double
    · exact Routine.randomFree_skip
  have setup : Command.RandomFree (RationalSelection.logSetup (O := O)).command := by
    simp [RationalSelection.logSetup]
  exact Command.RandomFree.seq setup (Routine.randomFree_iterate _ _ _ body)

theorem prepare_randomFree : Command.RandomFree (prepare (O := O)).command := by simp [prepare]

theorem bankRoutine_randomFree : Command.RandomFree (bankRoutine (O := O)).command := by
  have embedded := (logRoutine_randomFree (O := O)).mapSymbols Symbol.bit readBit |>.rename slots
  unfold bankRoutine
  exact Command.RandomFree.seq prepare_randomFree embedded

theorem routine_randomFree : Command.RandomFree (routine (O := O)).command := by
  exact Command.RandomFree.seq bankRoutine_randomFree (Routine.randomFree_assign _ _ _ _ _ _ _)


theorem input_bound_length (s : Store) : StoreBound (input s) (s 17).length := by
  intro j
  by_cases zero : j = 0 <;> simp [input, zero]

theorem bankRoutine_owned_bound (s : Store) (j : Fin 16) :
    (((bankRoutine (O := O)).eval s) (slots j)).length ≤ 4 * ((s 17).length + 1) := by
  rw [bankRoutine_owned, List.length_map]
  exact RationalSelection.logRoutine_bound (O := O) (input s) (s 17).length (input_bound_length s) j

theorem bankRoutine_scratch (s : Store) : (bankRoutine (O := O)).eval s 18 = [] := by
  have outside : ∀ i : Fin 16, (18 : Fin 32) ≠ slots i := by
    intro i same
    have equal := congrArg Fin.val same
    change 18 = i.val at equal
    have := i.isLt
    omega
  rw [bankRoutine_eval, bankStore, Memory.patchStore_outside slots _ _ 18 outside,
    preparedStore]
  simp

/-- Only the private logarithm workspace needs fresh room; all other caller
registers retain their existing common cap. -/
theorem routine_preserves_cap (s : Store) (cap : ℕ) (sizes : StoreBound s cap)
    (room : 4 * ((s 17).length + 1) ≤ cap) : StoreBound ((routine (O := O)).eval s) cap := by
  have bankBound : StoreBound ((bankRoutine (O := O)).eval s) cap := by
    intro j
    by_cases owned : j.val < 16
    · let privateIndex : Fin 16 := ⟨j.val, owned⟩
      have same : slots privateIndex = j := by apply Fin.ext; rfl
      rw [← same]
      exact (bankRoutine_owned_bound (O := O) s privateIndex).trans room
    · by_cases scratch : j = 18
      · subst j
        rw [bankRoutine_scratch]
        simp
      · rw [bankRoutine_frame (O := O) s j (by omega) scratch]
        exact sizes j
  exact bankBound.assign (O := O) 4 19 18 (by decide) (by decide) (by decide) id

end ComplexityOfGenerators.Examples.HAMPATH.Native.Logarithm
