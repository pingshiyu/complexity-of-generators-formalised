import ComplexityOfGenerators.Examples.HAMPATHNative.Rank
import ComplexityOfGenerators.Examples.HAMPATHNative.LogarithmBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def rankWorkspace (budget : ℕ) : ℕ := budget * budget + 10 * (budget + 1)

theorem rankWorkspace_large (budget : ℕ) :
    budget ≤ rankWorkspace budget ∧ 4 * (budget + 1) ≤ rankWorkspace budget ∧
      budget * budget ≤ rankWorkspace budget := by
  unfold rankWorkspace
  omega

theorem rankSetup_bound {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((rankSetup (O := O)).eval s) budget ∧ (rankSetup (O := O)).cost s ≤ 30 * (budget + 1) := by
  have copying := sizes.assign (O := O) 17 21 18 (by decide) (by decide) (by decide) id
  constructor
  · exact copying.clearMany [17, 19, 20]
  · have clearing := Routine.clearMany_cost (O := O) [17, 19, 20]
      ((Routine.assign (O := O) 17 21 18 (by decide) (by decide) (by decide) id).eval s)
      budget (by intro j _; exact copying j)
    have source := sizes 17
    have clock := sizes 21
    have scratch := sizes 18
    simp only [List.length_cons, List.length_nil] at clearing
    change (Routine.assign (O := O) 17 21 18 (by decide) (by decide) (by decide) id).cost s + 1 + _ ≤ _
    rw [Routine.assign_cost]
    omega

theorem rankIterate_bound {O : Type} (s : Store) (budget count : ℕ)
    (sizes : StoreBound s budget) (source : s 17 = []) (total : s 20 = []) (inside : count ≤ budget) :
    StoreBound (((rankCounted (O := O)).eval^[count]) s) (rankWorkspace budget) := by
  induction count with
  | zero => exact sizes.mono (rankWorkspace_large budget).1
  | succ count ih =>
      have before := ih (by omega)
      let current := (rankCounted (O := O)).eval^[count] s
      let popped := (Local.pop (S := Symbol) (21 : Fin 32)).eval current
      let bumped := (Local.push (S := Symbol) (17 : Fin 32) (.bit true)).eval popped
      let logged := (Logarithm.routine (O := O)).eval bumped
      change StoreBound current (rankWorkspace budget) at before
      have values := rankIterate_values (O := O) s source total count
      have sourceLength : (current 17).length = count := by
        simpa only [current, List.length_replicate] using congrArg List.length values.1
      have poppedBound : StoreBound popped (rankWorkspace budget) := before.update 21 _ (by
        have h := before 21
        change (current 21).tail.length ≤ rankWorkspace budget
        simp only [List.length_tail]
        omega)
      have bumpedBound : StoreBound bumped (rankWorkspace budget) := poppedBound.update 17 _ (by
        have room := (rankWorkspace_large budget).1
        simp [bumped, popped, Local.eval, Local.push, Local.pop, Action.apply, sourceLength]
        omega)
      have bumpedLength : (bumped 17).length = count + 1 := by
        simp [bumped, popped, Local.eval, Local.push, Local.pop, Action.apply, sourceLength]
      have loggedBound : StoreBound logged (rankWorkspace budget) :=
        Logarithm.routine_preserves_cap bumped _ bumpedBound (by
          rw [bumpedLength]
          have room := (rankWorkspace_large budget).2.1
          omega)
      rw [Function.iterate_succ_apply']
      intro j
      by_cases output : j = 20
      · subst j
        have next := (rankIterate_values (O := O) s source total (count + 1)).2.1
        rw [Function.iterate_succ_apply'] at next
        rw [next, List.length_replicate]
        have square := Nat.mul_le_mul inside inside
        exact (rank_le_square (count + 1)).trans (square.trans (rankWorkspace_large budget).2.2)
      · change ((Routine.transfer (O := O) 19 20 (by decide) id).eval logged j).length ≤ _
        by_cases emitted : j = 19
        · simp [Routine.transfer, emitted]
        · simpa [Routine.transfer, emitted, output] using loggedBound j

theorem rankCounted_cost {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget)
    (source : s 17 = []) (total : s 20 = []) (count : ℕ) (inside : count < budget) :
    (rankCounted (O := O)).cost ((rankCounted (O := O)).eval^[count] s) ≤
      1100 * (rankWorkspace budget + 1)^2 := by
  let current := (rankCounted (O := O)).eval^[count] s
  let popped := (Local.pop (S := Symbol) (21 : Fin 32)).eval current
  let bumped := (Local.push (S := Symbol) (17 : Fin 32) (.bit true)).eval popped
  let logged := (Logarithm.routine (O := O)).eval bumped
  have currentBound := rankIterate_bound (O := O) s budget count sizes source total (by omega)
  change StoreBound current (rankWorkspace budget) at currentBound
  have values := rankIterate_values (O := O) s source total count
  have sourceLength : (current 17).length = count := by
    simpa only [current, List.length_replicate] using congrArg List.length values.1
  have poppedBound : StoreBound popped (rankWorkspace budget) := currentBound.update 21 _ (by
    have h := currentBound 21
    change (current 21).tail.length ≤ rankWorkspace budget
    simp only [List.length_tail]
    omega)
  have bumpedBound : StoreBound bumped (rankWorkspace budget) := poppedBound.update 17 _ (by
    have room := (rankWorkspace_large budget).1
    simp [bumped, popped, Local.eval, Local.push, Local.pop, Action.apply, sourceLength]
    omega)
  have bounded := Logarithm.routine_bound (O := O) bumped (rankWorkspace budget) bumpedBound
  have emitted := bounded.1 19
  change 1 + 1 + (1 + 1 + ((Logarithm.routine (O := O)).cost bumped + 1 + 6 * (logged 19).length)) ≤ _
  have logCost := bounded.2
  change (logged 19).length ≤ _ at emitted
  nlinarith only [logCost, emitted]

theorem ranks_cost {O : Type} (s : Store) (budget : ℕ) (sizes : StoreBound s budget)
    (source : s 17 = []) (total : s 20 = []) (clock : (s 21).length ≤ budget) :
    (ranks (O := O)).cost s ≤ budget * (1200 * (rankWorkspace budget + 1)^2) := by
  have loop := Routine.loopCost_bound (rankCounted (O := O)).cost (rankCounted (O := O)).eval
    (s 21).length (1100 * (rankWorkspace budget + 1)^2) s (by
      intro i inside
      exact rankCounted_cost s budget sizes source total i (by omega))
  change Routine.loopCost (rankCounted (O := O)).cost (rankCounted (O := O)).eval (s 21).length s ≤ _
  apply loop.trans
  apply Nat.mul_le_mul clock
  have positive : 1 ≤ (rankWorkspace budget + 1)^2 := by
    nlinarith only [Nat.zero_le (rankWorkspace budget)]
  nlinarith only [positive]

theorem rankCore_cost {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget)
    (sizes : StoreBound s budget) :
    (rankCore (O := O)).cost s ≤ 2000 * (budget + 1) * (rankWorkspace budget + 1)^2 := by
  let a := (metadata (O := O)).eval s
  let b := (rankSetup (O := O)).eval a
  have aBound : StoreBound a budget := metadata_bound s budget positive sizes
  obtain ⟨bBound, setupCost⟩ := rankSetup_bound (O := O) a budget aBound
  change StoreBound b budget at bBound
  have source : b 17 = [] := by simp [b, rankSetup, Routine.seq, Routine.clearMany_eval]
  have total : b 20 = [] := by simp [b, rankSetup, Routine.seq, Routine.clearMany_eval]
  have loopCost := ranks_cost (O := O) b budget bBound source total (bBound 21)
  have output := (rankIterate_values (O := O) b source total (b 21).length).2.1
  have length : ((ranks (O := O)).eval b 20).length ≤ budget * budget := by
    have equal : ((ranks (O := O)).eval b 20).length = rank (b 21).length := by
      simpa only [ranks, Routine.iterate, rankCounted, List.length_replicate] using congrArg List.length output
    rw [equal]
    exact (rank_le_square _).trans (Nat.mul_le_mul (bBound 21) (bBound 21))
  have last := gate_cost (O := O) 20 ((ranks (O := O)).eval b)
  have first := metadata_cost (O := O) s budget sizes
  have room := (rankWorkspace_large budget).2.2
  have square : rankWorkspace budget ≤ (rankWorkspace budget + 1)^2 := by
    nlinarith only [Nat.zero_le (rankWorkspace budget)]
  have scalar := (rankWorkspace_large budget).1.trans square
  have quadratic := room.trans square
  have unit : 1 ≤ (rankWorkspace budget + 1)^2 := by
    nlinarith only [Nat.zero_le (rankWorkspace budget)]
  change (metadata (O := O)).cost s + 1 +
    ((rankSetup (O := O)).cost a + 1 + ((ranks (O := O)).cost b + 1 +
      (gate (O := O) 20).cost ((ranks (O := O)).eval b))) ≤ _
  nlinarith only [first, setupCost, loopCost, last, length, scalar, quadratic, unit,
    Nat.zero_le (budget * (rankWorkspace budget + 1)^2)]

theorem rankRoutine_randomFree : Command.RandomFree rankRoutine.command := by
  simp [rankRoutine, rankCore, prepare, parser_randomFree, metadata_randomFree, rankSetup,
    ranks, rankBody, Logarithm.routine_randomFree, gate_randomFree]

end ComplexityOfGenerators.Examples.HAMPATH.Native
