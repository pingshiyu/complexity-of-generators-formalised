import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Basic
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.DecodeBounds

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection

set_option backward.isDefEq.respectTransparency false

theorem pow_clog_le_twice (denominator : ℕ) (positive : 0 < denominator) :
    2 ^ Nat.clog 2 denominator ≤ 2 * denominator := by
  by_cases one : denominator = 1
  · simp [one, Nat.clog_one_right]
  · have large : 1 < denominator := by omega
    have exponent := Nat.clog_pos (by decide : 1 < 2) large
    have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) large
    have successor : (Nat.clog 2 denominator).pred + 1 = Nat.clog 2 denominator :=
      Nat.succ_pred_eq_of_pos exponent
    rw [← successor, Nat.pow_succ]
    omega

theorem compare_preserves_bound {O : Type} (slots : Compare.Layout 16) (s : Store) (budget : ℕ)
    (positive : 1 ≤ budget) (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((Compare.routine (O := O) slots true).eval s j).length ≤ budget := by
  intro j
  rw [Compare.routine_eval]
  by_cases flag : j = slots 2 <;> by_cases copy : j = slots 3 <;>
    by_cases counter : j = slots 4 <;> by_cases scratch : j = slots 5 <;>
      simp [flag, copy, counter, scratch] <;>
      (try split_ifs) <;> (try simp only [List.length_nil, List.length_singleton]) <;>
      first | exact sizes _ | omega

theorem finish_bound {O : Type} (s : Store) (budget : ℕ)
    (positive : 1 ≤ budget) (sizes : ∀ j, (s j).length ≤ budget) :
    ∀ j, ((finish (O := O)).eval s j).length ≤ budget :=
  compare_preserves_bound numeratorSlots _ budget positive
    (compare_preserves_bound denominatorSlots s budget positive sizes)

theorem finish_cost {O : Type} (s : Store) (budget : ℕ)
    (positive : 1 ≤ budget) (sizes : ∀ j, (s j).length ≤ budget) :
    (finish (O := O)).cost s ≤ 160 * (budget + 1) + 1 := by
  have first := Compare.routine_cost (O := O) denominatorSlots true s budget sizes
  have last := Compare.routine_cost (O := O) numeratorSlots true
    ((Compare.routine (O := O) denominatorSlots true).eval s) budget
    (compare_preserves_bound denominatorSlots s budget positive sizes)
  change (Compare.routine (O := O) denominatorSlots true).cost s + 1 +
    (Compare.routine (O := O) numeratorSlots true).cost
      ((Compare.routine (O := O) denominatorSlots true).eval s) ≤ _
  omega

theorem selector_bound {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) (positive : 0 < (s 0).length)
    (enough : Nat.clog 2 (s 0).length ≤ (s 2).length) :
    ∀ j, ((selector (O := O)).eval s j).length ≤ 20 * (budget + 1) := by
  let logged : Store := (logRoutine (O := O)).eval s
  let decoded : Store := (decodeRoutine (O := O)).eval logged
  have logSizes := logRoutine_bound (O := O) s budget sizes
  have bitCount : logged 4 = List.replicate (Nat.clog 2 (s 0).length) true := (logRoutine_values s).2
  have originalBits : logged 2 = s 2 := logRoutine_input s 2 (by simp)
  have range : 2 ^ (logged 4).length ≤ workspace budget := by
    rw [bitCount, List.length_replicate]
    have bound := pow_clog_le_twice (s 0).length positive
    have source := sizes 0
    unfold workspace
    omega
  have decodeSizes := decodeRoutine_bound (O := O) logged (workspace budget) logSizes
    (by simpa [bitCount, originalBits] using enough) range
  have finishSizes := finish_bound (O := O) decoded (workspace (workspace budget))
    (by unfold workspace; omega) decodeSizes
  intro j
  have bound := finishSizes j
  change ((selector (O := O)).eval s j).length ≤ _ at bound
  exact bound.trans (by unfold workspace; omega)

theorem selector_cost {O : Type} (s : Store) (budget : ℕ)
    (sizes : ∀ j, (s j).length ≤ budget) (positive : 0 < (s 0).length)
    (enough : Nat.clog 2 (s 0).length ≤ (s 2).length) :
    (selector (O := O)).cost s ≤ 20000 * (budget + 1) ^ 2 := by
  let logged : Store := (logRoutine (O := O)).eval s
  let decoded : Store := (decodeRoutine (O := O)).eval logged
  have logSizes := logRoutine_bound (O := O) s budget sizes
  have bitCount : logged 4 = List.replicate (Nat.clog 2 (s 0).length) true := (logRoutine_values s).2
  have originalBits : logged 2 = s 2 := logRoutine_input s 2 (by simp)
  have range : 2 ^ (logged 4).length ≤ workspace budget := by
    rw [bitCount, List.length_replicate]
    have bound := pow_clog_le_twice (s 0).length positive
    have source := sizes 0
    unfold workspace
    omega
  have enoughBits : (logged 4).length ≤ (logged 2).length := by simpa [bitCount, originalBits] using enough
  have decodeSizes := decodeRoutine_bound (O := O) logged (workspace budget) logSizes enoughBits range
  have first := logRoutine_cost (O := O) s budget sizes
  have second := decodeRoutine_cost (O := O) logged (workspace budget) logSizes enoughBits range
  have last := finish_cost (O := O) decoded (workspace (workspace budget))
    (by unfold workspace; omega) decodeSizes
  change (logRoutine (O := O)).cost s + 1 + ((decodeRoutine (O := O)).cost logged + 1 +
    (finish (O := O)).cost decoded) ≤ _
  unfold workspace at second last
  nlinarith

/-- The reported polynomial counts actual primitive stack transitions.
The routine reads its selector coins from stack 2, preserving the random head
of the surrounding phase that precollected the fixed block. -/
theorem selector_runs {O : Type} {n : ℕ} (bits : BitString) (m : Memory Bool O 16)
    (index : m.indexHead ≤ n) (budget : ℕ)
    (sizes : ∀ j, (m.store j).length ≤ budget) (positive : 0 < (m.store 0).length)
    (enough : Nat.clog 2 (m.store 0).length ≤ (m.store 2).length) :
    ∃ ticks ≤ 20000 * (budget + 1) ^ 2,
      (selector (O := O)).command.Runs n bits m ticks (.done {m with store := (selector (O := O)).eval m.store}) := by
  obtain ⟨ticks, cost, run⟩ := (selector (O := O)).runs (n := n) bits m index
  exact ⟨ticks, cost.trans (selector_cost m.store budget sizes positive enough), run⟩

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection
