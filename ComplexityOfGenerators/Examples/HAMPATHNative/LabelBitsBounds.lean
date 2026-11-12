import ComplexityOfGenerators.Examples.HAMPATHNative.LabelBits
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.LabelBits

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem input_bound (s : Store) (budget : ℕ) (sizes : StoreBound s budget) : StoreBound (input s) (2 * budget) := by
  intro j
  have label := sizes 25
  have width := sizes 19
  by_cases bits : j = 2 <;> by_cases clock : j = 4 <;> simp [input, bits, clock] <;> omega

theorem prepare_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((prepare (O := O)).eval s) (2 * budget) := by
  have label := sizes 25
  have width := sizes 19
  intro j
  rw [prepare_eval]
  by_cases owned : j.val < 16 <;> by_cases bits : j = 2 <;> by_cases clock : j = 4 <;>
    by_cases scratch : j = 18 <;> simp [preparedStore, owned, bits, clock, scratch] <;>
    first | exact (sizes _).trans (by omega) | omega

theorem prepare_cost {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    (prepare (O := O)).cost s ≤ 150 * (budget + 1) := by
  let registers : List (Fin 32) := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15]
  let a := (Routine.clearMany (O := O) registers).eval s
  let b := (Routine.assign (O := O) 19 2 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit false)).eval a
  let c := (Routine.copy (O := O) 25 2 18 (by decide) (by decide) (by decide) (fun x => Symbol.bit (readBit x))).eval b
  have aBound : StoreBound a budget := sizes.clearMany registers
  have bBound : StoreBound b budget := aBound.assign 19 2 18 (by decide) (by decide) (by decide) _
  have cBound : StoreBound c (2 * budget) := by
    change StoreBound (Function.update (Function.update b 18 []) 2
      ((b 25).map (fun x => Symbol.bit (readBit x)) ++ b 2)) _
    apply ((bBound.mono (by omega : budget ≤ 2 * budget)).clear 18).update 2
    simp only [List.length_append, List.length_map]
    have left := bBound 25
    have right := bBound 2
    omega
  have clearing := Routine.clearMany_cost (O := O) registers s budget (by intro j _; exact sizes j)
  have assignFirst : (Routine.assign (O := O) 19 2 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit false)).cost a ≤
      20 * budget + 3 := by rw [Routine.assign_cost]; have := aBound 2; have := aBound 18; have := aBound 19; omega
  have copying : (Routine.copy (O := O) 25 2 18 (by decide) (by decide) (by decide) (fun x => Symbol.bit (readBit x))).cost b ≤
      17 * budget + 2 := by change 3 * (b 18).length + 14 * (b 25).length + 2 ≤ _; have := bBound 18; have := bBound 25; omega
  have assignLast : (Routine.assign (O := O) 19 4 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost c ≤
      40 * budget + 3 := by rw [Routine.assign_cost]; have := cBound 4; have := cBound 18; have := cBound 19; omega
  have registerLength : registers.length = 16 := rfl
  rw [registerLength] at clearing
  change (Routine.clearMany (O := O) registers).cost s + 1 +
    ((Routine.assign (O := O) 19 2 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit false)).cost a + 1 +
      ((Routine.copy (O := O) 25 2 18 (by decide) (by decide) (by decide) (fun x => Symbol.bit (readBit x))).cost b + 1 +
        (Routine.assign (O := O) 19 4 18 (by decide) (by decide) (by decide) (fun _ => Symbol.bit true)).cost c)) ≤ _
  omega

theorem bankRoutine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget)
    (range : 2 ^ (s 19).length ≤ budget) :
    StoreBound ((bankRoutine (O := O)).eval s) (10 * (budget + 1)) := by
  have source := input_bound s budget sizes
  have localBound := RationalSelection.decodeRoutine_bound (O := O) (input s) (2 * budget) source
    (input_enough s) (by simpa [input] using (range.trans (by omega : budget ≤ 2 * budget)))
  have prepared := prepare_bound (O := O) s budget sizes
  intro j
  by_cases owned : j.val < 16
  · let privateIndex : Fin 16 := ⟨j.val, owned⟩
    have same : Logarithm.slots privateIndex = j := by apply Fin.ext; rfl
    rw [← same, bankRoutine_owned, List.length_map]
    have bound := localBound privateIndex
    unfold RationalSelection.workspace at bound
    omega
  · have outside : ∀ i : Fin 16, j ≠ Logarithm.slots i := by
      intro i same
      have equal := congrArg Fin.val same
      change j.val = i.val at equal
      have := i.isLt
      omega
    rw [bankRoutine_eval, bankStore, Memory.patchStore_outside Logarithm.slots _ _ j outside]
    have small : (preparedStore s j).length ≤ 2 * budget := by simpa only [prepare_eval] using prepared j
    omega

theorem routine_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget)
    (range : 2 ^ (s 19).length ≤ budget) :
    StoreBound ((routine (O := O)).eval s) (10 * (budget + 1)) ∧
      (routine (O := O)).cost s ≤ 2000 * (budget + 1)^2 := by
  have bankBound := bankRoutine_bound (O := O) s budget sizes range
  have first := prepare_cost (O := O) s budget sizes
  have decoder := RationalSelection.decodeRoutine_cost (O := O) (input s) (2 * budget)
    (input_bound s budget sizes) (input_enough s)
    (by simpa [input] using range.trans (by omega : budget ≤ 2 * budget))
  constructor
  · exact bankBound.assign 5 28 18 (by decide) (by decide) (by decide) id
  · change (bankRoutine (O := O)).cost s + 1 +
      (Routine.assign (O := O) 5 28 18 (by decide) (by decide) (by decide) id).cost ((bankRoutine (O := O)).eval s) ≤ _
    rw [bankRoutine_cost, Routine.assign_cost]
    have source := bankBound 5
    have target := bankBound 28
    have scratch := bankBound 18
    nlinarith only [first, decoder, source, target, scratch]

theorem decodeRoutine_randomFree {O : Type} : Command.RandomFree (RationalSelection.decodeRoutine (O := O)).command := by
  have body : Command.RandomFree (RationalSelection.decodeBody (O := O)).command := by
    rw [RationalSelection.decodeBody, Routine.randomFree_seq]
    constructor
    · apply (Routine.randomFree_branch _ _).mpr
      intro bit
      split <;> simp
    · simp [RationalSelection.doubleWeight]
  have setup : Command.RandomFree (RationalSelection.decodeSetup (O := O)).command := by
    simp [RationalSelection.decodeSetup]
  exact .seq setup (Routine.randomFree_iterate _ _ _ body)

theorem routine_randomFree {O : Type} : Command.RandomFree (routine (O := O)).command := by
  have embedded := (decodeRoutine_randomFree (O := O)).mapSymbols Symbol.bit readBit |>.rename Logarithm.slots
  have prepared : Command.RandomFree (prepare (O := O)).command := by simp [prepare]
  have bank : Command.RandomFree (bankRoutine (O := O)).command := by
    unfold bankRoutine
    exact .seq prepared embedded
  exact .seq bank (Routine.randomFree_assign _ _ _ _ _ _ _)

end ComplexityOfGenerators.Examples.HAMPATH.Native.LabelBits
