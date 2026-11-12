import ComplexityOfGenerators.Examples.HAMPATHNative.RowModel

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem cellIterate_diagonal (state : CellState) (count : ℕ) :
    (cellStep^[count] state).diagonal ≤ state.diagonal := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      exact (ih (cellStep state)).trans (by simp [cellStep])

theorem cellIterate_word (state : CellState) (count : ℕ) :
    (cellStep^[count] state).word = state.word.drop count := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, ih]; simp [cellStep, List.drop_tail]

theorem rowIterate_word_le (size count : ℕ) (state : RowState) :
    (((rowStep size)^[count] state).word).length ≤ state.word.length := by
  induction count generalizing state with
  | zero => rfl
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      apply (ih (rowStep size state)).trans
      simp [rowStep, cellIterate_word]

theorem rowRoutine_cost {O : Type} (base : Store) (size : ℕ) (state : RowState) (clock : List Symbol) :
    (rowRoutine (O := O)).cost (rowEncoded base size state clock) ≤ 60 * (state.row + size + 1) := by
  let initial := rowEncoded base size state clock
  let prepared := cellEncoded initial ⟨state.word, state.row, true, state.valid⟩
    (List.replicate size (.bit true))
  let scanned := cellEncoded initial (cellStep^[size] ⟨state.word, state.row, true, state.valid⟩) []
  have diagonal := cellIterate_diagonal ⟨state.word, state.row, true, state.valid⟩ size
  have prepareCost : (rowPrepare (O := O)).cost initial ≤ 14 * state.row + 14 * size + 10 := by
    simp [rowPrepare, initial, rowEncoded, cellEncoded, flag, Routine.seq, Routine.assign_cost,
      Routine.assign_eval, Routine.ofLocal, Local.ticks, Local.push, Local.eval, Action.apply]
    omega
  have cellsCost : (cells (O := O)).cost prepared ≤ 16 * size := by
    simpa [prepared, cellEncoded] using cells_cost (O := O) prepared
  have clearCost := Routine.clearMany_cost (O := O) ([3, 8, 9, 10] : List (Fin 32)) scanned
    (state.row + 1) (by
      intro j member
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      · simpa [scanned, cellEncoded] using diagonal.trans (Nat.le_succ _)
      · simp only [scanned, cellEncoded, Function.update_apply]
        simp [flag]; split <;> simp <;> omega
      · simp [scanned, cellEncoded, initial, rowEncoded]
      · simp [scanned, cellEncoded])
  have finishCost : (rowFinish (O := O)).cost scanned ≤ 12 * (state.row + 1) + 6 := by
    simp only [List.length_cons, List.length_nil] at clearCost
    change (Routine.clearMany (O := O) [3, 8, 9, 10]).cost scanned + 1 + 1 ≤ _
    omega
  change (rowPrepare (O := O)).cost initial + 1 +
    ((cells (O := O)).cost ((rowPrepare (O := O)).eval initial) + 1 +
      (rowFinish (O := O)).cost ((cells (O := O)).eval ((rowPrepare (O := O)).eval initial))) ≤ _
  rw [show (rowPrepare (O := O)).eval initial = prepared from rowPrepare_eval (O := O) base size state clock,
    show (cells (O := O)).eval prepared = scanned from cells_eval (O := O) initial _ size]
  omega

theorem rows_cost {O : Type} (base : Store) (size : ℕ) (state : RowState) (count : ℕ) :
    (rows (O := O)).cost (rowEncoded base size state (List.replicate count (.bit true))) ≤
      count * (64 * (state.row + count + size + 1)) := by
  have bounded := Routine.loopCost_bound (rowCounted (O := O)).cost (rowCounted (O := O)).eval
    count (60 * (state.row + count + size + 1) + 2)
    (rowEncoded base size state (List.replicate count (.bit true))) (by
      intro i inside
      rw [rowIterate_eval]
      simp only [rowCounted, Routine.counted, Routine.seq, Routine.ofLocal, Local.pop, Local.ticks]
      have popped : (Local.pop 5).eval
          (rowEncoded base size ((rowStep size)^[i] state) ((List.replicate count (.bit true)).drop i)) =
          rowEncoded base size ((rowStep size)^[i] state) (((List.replicate count (.bit true)).drop i).tail) := by
        funext j
        fin_cases j <;> simp [Local.eval_pop, rowEncoded, cellEncoded]
      change (Local.act 5 Action.pop).eval
          (rowEncoded base size ((rowStep size)^[i] state) ((List.replicate count (.bit true)).drop i)) = _ at popped
      rw [popped]
      have stepCost := rowRoutine_cost (O := O) base size ((rowStep size)^[i] state)
        (((List.replicate count (.bit true)).drop i).tail)
      rw [rowIterate_number] at stepCost
      omega)
  change Routine.loopCost (rowCounted (O := O)).cost (rowCounted (O := O)).eval
    ((rowEncoded base size state (List.replicate count (.bit true))) 5).length
    (rowEncoded base size state (List.replicate count (.bit true))) ≤ _
  rw [show rowEncoded base size state (List.replicate count (.bit true)) 5 = List.replicate count (.bit true) by
    simp [rowEncoded]]
  simp only [List.length_replicate]
  apply bounded.trans
  apply Nat.mul_le_mul_left
  omega

end ComplexityOfGenerators.Examples.HAMPATH.Native
