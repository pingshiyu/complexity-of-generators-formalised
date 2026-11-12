import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Power

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection

set_option backward.isDefEq.respectTransparency false

def workspace (budget : ℕ) : ℕ := 4 * (budget + 1)

theorem logSetup_bound {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((logSetup (O := O)).eval s j).length ≤ workspace budget := by
  intro j
  have large : budget + 1 ≤ workspace budget := by unfold workspace; omega
  fin_cases j <;>
    simp [logSetup, Routine.seq, Routine.clearMany_eval, Routine.ofLocal, Routine.assign_eval] <;>
    first | exact (sizes _).trans (by omega) | omega

theorem logBody_bound {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ workspace budget) (denominator : (s 0).length ≤ budget)
    (bits : (s 4).length + 1 ≤ workspace budget) :
    ∀ j, ((logBody (O := O)).eval s j).length ≤ workspace budget := by
  have h₀ := sizes 0
  have h₁ := sizes 1
  have h₂ := sizes 2
  have h₃ := sizes 3
  have h₄ := sizes 4
  have h₅ := sizes 5
  have h₁₀ := sizes 10
  have h₁₁ := sizes 11
  have h₁₂ := sizes 12
  have h₁₃ := sizes 13
  have h₁₄ := sizes 14
  have h₁₅ := sizes 15
  have large : 2 * budget + 1 ≤ workspace budget := by unfold workspace; omega
  intro j
  fin_cases j <;>
    simp [logBody, Routine.seq, Routine.branch, Compare.routine_eval, powerSlots,
      doublePower, Routine.assign_eval, Routine.copy, Routine.ofLocal, Routine.skip] <;>
    (try split_ifs) <;> (try simp [Local.eval]) <;> omega

theorem logIterate_bound {O : Type} (s : Store) (budget steps : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) (stepsBound : steps ≤ (s 0).length) :
    ∀ j, (((logCounted (O := O)).eval^[steps] ((logSetup (O := O)).eval s)) j).length ≤ workspace budget := by
  induction steps with
  | zero => exact logSetup_bound s budget sizes
  | succ steps ih =>
    let current : Store := (logCounted (O := O)).eval^[steps] ((logSetup (O := O)).eval s)
    have oldSizes := ih (by omega)
    change ∀ j, (current j).length ≤ workspace budget at oldSizes
    have poppedSizes : ∀ j, ((Function.update current 10 (current 10).tail) j).length ≤ workspace budget := by
      intro j
      by_cases clock : j = 10
      · subst j
        simp only [Function.update_self, List.length_tail]
        have := oldSizes 10
        omega
      · simpa [clock] using oldSizes j
    have source : (current 0).length ≤ budget := by
      change (((logCounted (O := O)).eval^[steps] ((logSetup (O := O)).eval s)) 0).length ≤ _
      rw [logIterate_input s steps 0 (by simp)]
      exact sizes 0
    have count : (current 4).length + 1 ≤ workspace budget := by
      have values := (logIterate_values (O := O) s steps).2
      change current 4 = _ at values
      have large : budget + 1 ≤ workspace budget := by unfold workspace; omega
      change (current 4).length + 1 ≤ _
      rw [values, List.length_replicate]
      have := sizes 0
      omega
    rw [Function.iterate_succ_apply']
    exact logBody_bound (O := O) (Function.update current 10 (current 10).tail) budget poppedSizes
      (by simpa using source) (by simpa using count)

theorem logRoutine_bound {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((logRoutine (O := O)).eval s j).length ≤ workspace budget := by
  have bound := logIterate_bound (O := O) s budget (s 0).length sizes le_rfl
  simpa [logRoutine, Routine.seq, Routine.iterate,
    (logSetup_initial s).2.2.2.2.2, logCounted] using bound

theorem doublePower_cost {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) : (doublePower (O := O)).cost s ≤ 34 * budget + 8 := by
  have power := sizes 3
  have scratch := sizes 9
  have temporary := sizes 11
  simp [doublePower, Routine.seq, Routine.assign_cost, Routine.assign_eval,
    Routine.copy, Routine.ofLocal, Local.ticks, Local.push]
  omega

theorem comparison_bound {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget)
    (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((Compare.routine (O := O) powerSlots true).eval s j).length ≤ budget := by
  intro j
  fin_cases j <;> simp [Compare.routine_eval, powerSlots] <;>
    (try split_ifs) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
    first | exact sizes _ | omega

theorem logBody_cost {O : Type} (s : Store) (budget : ℕ) (positive : 1 ≤ budget)
    (sizes : ∀ j, (s j).length ≤ budget) : (logBody (O := O)).cost s ≤ 120 * (budget + 1) := by
  let compared : Store := (Compare.routine (O := O) powerSlots true).eval s
  have first := Compare.routine_cost (O := O) powerSlots true s budget sizes
  have last := doublePower_cost (O := O) compared budget (comparison_bound s budget positive sizes)
  change (Compare.routine (O := O) powerSlots true).cost s + 1 +
    (1 + (if (compared 6).head?.isSome then doublePower else Routine.skip).cost compared) ≤ _
  by_cases flag : (compared 6).head?.isSome
  · simp only [flag, ite_true]
    omega
  · simp [flag, Routine.skip, Routine.ofLocal, Local.ticks]
    omega

theorem logSetup_cost {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) : (logSetup (O := O)).cost s ≤ 56 * budget + 20 := by
  have cleared := Routine.clearMany_cost (O := O)
    [3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15] s budget (by intro j _; exact sizes j)
  have denominator := sizes 0
  simp only [List.length_cons, List.length_nil] at cleared
  simp [logSetup, Routine.seq, Routine.ofLocal, Local.ticks, Local.push,
    Routine.assign_cost, Routine.clearMany_eval, Local.eval]
  omega

theorem logRoutine_cost {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) : (logRoutine (O := O)).cost s ≤ 600 * (budget + 1) ^ 2 := by
  have setupCost := logSetup_cost (O := O) s budget sizes
  have loopCost := Routine.loopCost_bound (logCounted (O := O)).cost (logCounted (O := O)).eval
    (s 0).length (120 * (workspace budget + 1) + 2) ((logSetup (O := O)).eval s) (by
      intro i inside
      let current : Store := (logCounted (O := O)).eval^[i] ((logSetup (O := O)).eval s)
      have bounds := logIterate_bound (O := O) s budget i sizes (by omega)
      change ∀ j, (current j).length ≤ workspace budget at bounds
      have popped : ∀ j, ((Function.update current 10 (current 10).tail) j).length ≤ workspace budget := by
        intro j
        by_cases clock : j = 10
        · subst j; simp only [Function.update_self, List.length_tail]; have := bounds 10; omega
        · simpa [clock] using bounds j
      have cost := logBody_cost (O := O) (Function.update current 10 (current 10).tail)
        (workspace budget) (by unfold workspace; omega) popped
      change 1 + 1 + (logBody (O := O)).cost (Function.update current 10 (current 10).tail) ≤ _
      omega)
  change (logSetup (O := O)).cost s + 1 +
    Routine.loopCost (logCounted (O := O)).cost (logCounted (O := O)).eval
      (((logSetup (O := O)).eval s 10).length) ((logSetup (O := O)).eval s) ≤ _
  rw [(logSetup_initial s).2.2.2.2.2]
  have denominator := sizes 0
  unfold workspace at loopCost
  nlinarith

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection
