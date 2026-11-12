import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Decode
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.PowerBounds

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection

set_option backward.isDefEq.respectTransparency false

theorem decodeSetup_bound {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((decodeSetup (O := O)).eval s j).length ≤ workspace budget := by
  intro j
  have large : budget + 1 ≤ workspace budget := by unfold workspace; omega
  fin_cases j <;> simp [decodeSetup, Routine.seq, Routine.clear, Routine.ofLocal] <;>
    first | exact (sizes _).trans (by omega) | omega

theorem decodeBody_bound {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget)
    (power : 2 * (s 3).length ≤ budget) (value : (s 3).length + (s 5).length ≤ budget) :
    ∀ j, ((decodeBody (O := O)).eval s j).length ≤ budget := by
  have h₀ := sizes 0
  have h₁ := sizes 1
  have h₂ := sizes 2
  have h₃ := sizes 3
  have h₄ := sizes 4
  have h₅ := sizes 5
  have h₆ := sizes 6
  have h₇ := sizes 7
  have h₈ := sizes 8
  have h₉ := sizes 9
  have h₁₀ := sizes 10
  have h₁₁ := sizes 11
  have h₁₂ := sizes 12
  have h₁₃ := sizes 13
  have h₁₄ := sizes 14
  have h₁₅ := sizes 15
  intro j
  fin_cases j <;>
    simp [decodeBody, Routine.seq, Routine.branch, Routine.copy, doubleWeight,
      Routine.assign_eval, Routine.ofLocal, Routine.skip] <;>
    (try split_ifs) <;>
    (try simp [Local.eval, List.length_append]) <;> omega

theorem decodeIterate_bound {O : Type} (s : Store) (budget steps : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget)
    (enough : (s 4).length ≤ (s 2).length) (range : 2 ^ (s 4).length ≤ budget)
    (stepsBound : steps ≤ (s 4).length) :
    ∀ j, (((decodeCounted (O := O)).eval^[steps] ((decodeSetup (O := O)).eval s)) j).length ≤ workspace budget := by
  induction steps with
  | zero => exact decodeSetup_bound s budget sizes
  | succ steps ih =>
    let current : Store := (decodeCounted (O := O)).eval^[steps] ((decodeSetup (O := O)).eval s)
    have oldSizes := ih (by omega)
    change ∀ j, (current j).length ≤ workspace budget at oldSizes
    have poppedSizes : ∀ j, ((Function.update current 4 (current 4).tail) j).length ≤ workspace budget := by
      intro j
      by_cases clock : j = 4
      · subst j; simp only [Function.update_self, List.length_tail]; have := oldSizes 4; omega
      · simpa [clock] using oldSizes j
    have enoughNow : steps ≤ (s 2).length := by omega
    have values := decodeIterate_values (O := O) s steps enoughNow
    change current 3 = _ ∧ current 5 = _ ∧ current 2 = _ at values
    have nextRange : 2 * 2 ^ steps ≤ budget := by
      have exponent := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) stepsBound
      rw [Nat.pow_succ] at exponent
      omega
    have power : 2 * (current 3).length ≤ workspace budget := by
      rw [values.1, List.length_replicate]
      have : budget ≤ workspace budget := by unfold workspace; omega
      omega
    have number : (current 3).length + (current 5).length ≤ workspace budget := by
      rw [values.1, values.2.1, List.length_replicate, List.length_replicate]
      have decoded := FixedBitBlocks.decode_bound ((s 2).take steps)
      rw [List.length_take, Nat.min_eq_left enoughNow] at decoded
      have : budget ≤ workspace budget := by unfold workspace; omega
      omega
    rw [Function.iterate_succ_apply']
    exact decodeBody_bound (O := O) (Function.update current 4 (current 4).tail)
      (workspace budget) poppedSizes (by simpa using power) (by simpa using number)

theorem decodeRoutine_bound {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget)
    (enough : (s 4).length ≤ (s 2).length) (range : 2 ^ (s 4).length ≤ budget) :
    ∀ j, ((decodeRoutine (O := O)).eval s j).length ≤ workspace budget := by
  have bound := decodeIterate_bound (O := O) s budget (s 4).length sizes enough range le_rfl
  simpa [decodeRoutine, Routine.seq, Routine.iterate,
    (decodeSetup_initial s).2.2.2.2.1, decodeCounted] using bound

theorem decodeBody_cost {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) : (decodeBody (O := O)).cost s ≤ 60 * (budget + 1) := by
  have power := sizes 3
  have scratch := sizes 9
  have temporary := sizes 11
  simp [decodeBody, Routine.seq, Routine.branch, Routine.copy, doubleWeight,
    Routine.assign_cost, Routine.assign_eval, Routine.ofLocal, Local.ticks, Local.pop]
  split_ifs <;> simp [Routine.skip, Routine.ofLocal, Local.ticks, Local.eval] <;> omega

theorem decodeSetup_cost {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) : (decodeSetup (O := O)).cost s ≤ 6 * budget + 3 := by
  have power := sizes 3
  have value := sizes 5
  simp [decodeSetup, Routine.seq, Routine.clear, Routine.ofLocal, Local.ticks, Local.push]
  omega

theorem decodeRoutine_cost {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget)
    (enough : (s 4).length ≤ (s 2).length) (range : 2 ^ (s 4).length ≤ budget) :
    (decodeRoutine (O := O)).cost s ≤ 300 * (budget + 1) ^ 2 := by
  have setupCost := decodeSetup_cost (O := O) s budget sizes
  have loopCost := Routine.loopCost_bound (decodeCounted (O := O)).cost (decodeCounted (O := O)).eval
    (s 4).length (60 * (workspace budget + 1) + 2) ((decodeSetup (O := O)).eval s) (by
      intro i inside
      let current : Store := (decodeCounted (O := O)).eval^[i] ((decodeSetup (O := O)).eval s)
      have bounds := decodeIterate_bound (O := O) s budget i sizes enough range (by omega)
      change ∀ j, (current j).length ≤ workspace budget at bounds
      have popped : ∀ j, ((Function.update current 4 (current 4).tail) j).length ≤ workspace budget := by
        intro j
        by_cases clock : j = 4
        · subst j; simp only [Function.update_self, List.length_tail]; have := bounds 4; omega
        · simpa [clock] using bounds j
      have cost := decodeBody_cost (O := O) (Function.update current 4 (current 4).tail) (workspace budget) popped
      change 1 + 1 + (decodeBody (O := O)).cost (Function.update current 4 (current 4).tail) ≤ _
      omega)
  change (decodeSetup (O := O)).cost s + 1 +
    Routine.loopCost (decodeCounted (O := O)).cost (decodeCounted (O := O)).eval
      (((decodeSetup (O := O)).eval s 4).length) ((decodeSetup (O := O)).eval s) ≤ _
  rw [(decodeSetup_initial s).2.2.2.2.1]
  have clock := sizes 4
  unfold workspace at loopCost
  nlinarith

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection
