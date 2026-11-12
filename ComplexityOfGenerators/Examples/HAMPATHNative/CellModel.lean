import ComplexityOfGenerators.Examples.HAMPATHNative.Cell

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

theorem cellStep_invalid (state : CellState) (invalid : state.valid = false) :
    (cellStep state).valid = false := by simp [cellStep, invalid]

theorem cellIterate_invalid (state : CellState) (invalid : state.valid = false) (count : ℕ) :
    (cellStep^[count] state).valid = false := by
  induction count generalizing state with
  | zero => exact invalid
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      exact ih (cellStep state) (cellStep_invalid state invalid)

theorem cellIterate_initialValid (state : CellState) (count : ℕ)
    (accepted : (cellStep^[count] state).valid = true) : state.valid = true := by
  cases valid : state.valid with
  | true => rfl
  | false => rw [cellIterate_invalid state valid count] at accepted; cases accepted

/-- A successful row scan consumed exactly one Boolean row, and the selected
diagonal cell is false. The statement also covers arbitrary malformed input. -/
theorem cellIterate_sound (count : ℕ) (state : CellState)
    (accepted : (cellStep^[count] state).valid = true) :
    ∃ row : List Bool, row.length = count ∧
      state.word = row.map Symbol.bit ++ (cellStep^[count] state).word ∧
      (state.pending = true → state.diagonal < count → row[state.diagonal]? = some false) := by
  induction count generalizing state with
  | zero => exact ⟨[], rfl, by simp, by omega⟩
  | succ count ih =>
      rw [Function.iterate_succ_apply] at accepted ⊢
      have first := cellIterate_initialValid (cellStep state) count accepted
      cases word : state.word with
      | nil => simp [cellStep, word] at first
      | cons head rest =>
          cases head with
          | separator => simp [cellStep, word] at first
          | bit value =>
              obtain ⟨row, length, reconstruct, diagonal⟩ := ih (cellStep state) accepted
              refine ⟨value :: row, by simp [length], ?_, ?_⟩
              · change Symbol.bit value :: rest = Symbol.bit value :: (row.map Symbol.bit ++ _)
                congr 1
                simpa [cellStep, word] using reconstruct
              · intro pending inside
                cases diagonalEq : state.diagonal with
                | zero =>
                    have valueFalse : value = false := by
                      cases value with
                      | false => rfl
                      | true => simp [cellStep, word, diagonalEq, pending] at first
                    simp [diagonalEq, valueFalse]
                | succ column =>
                    have nextPending : (cellStep state).pending = true := by simp [cellStep, diagonalEq, pending]
                    have nextDiagonal : (cellStep state).diagonal = column := by simp [cellStep, diagonalEq]
                    have found := diagonal nextPending (by simp [nextDiagonal]; omega)
                    simpa [nextDiagonal, diagonalEq] using found

/-- Every Boolean row with a false diagonal survives the same executable
cell loop, leaving the suffix untouched. -/
theorem cellIterate_complete (row : List Bool) (tail : List Symbol) (diagonal : ℕ) (pending : Bool)
    (good : pending = true → diagonal < row.length → row[diagonal]? = some false) :
    let result := cellStep^[row.length] ⟨row.map Symbol.bit ++ tail, diagonal, pending, true⟩
    result.valid = true ∧ result.word = tail := by
  induction row generalizing diagonal pending with
  | nil => simp
  | cons value row ih =>
      have allowed : (!(value && decide (diagonal = 0) && pending) : Bool) = true := by
        by_cases zero : diagonal = 0
        · subst diagonal
          cases pending with
          | false => simp
          | true =>
              have found := good rfl (by simp)
              have valueFalse : value = false := by simpa using found
              simp [valueFalse]
        · simp [zero]
      have nextGood : (if diagonal = 0 then false else pending) = true →
          diagonal - 1 < row.length → row[diagonal - 1]? = some false := by
        intro nextPending inside
        cases diagonal with
        | zero => simp at nextPending
        | succ diagonal =>
            have oldPending : pending = true := by simpa using nextPending
            have found := good oldPending (by simp; omega)
            simpa using found
      have rest := ih (diagonal - 1) (if diagonal = 0 then false else pending) nextGood
      change (cellStep^[row.length]
        ⟨row.map Symbol.bit ++ tail, diagonal - 1, if diagonal = 0 then false else pending,
          !(value && decide (diagonal = 0) && pending)⟩).valid = true ∧
        (cellStep^[row.length]
          ⟨row.map Symbol.bit ++ tail, diagonal - 1, if diagonal = 0 then false else pending,
            !(value && decide (diagonal = 0) && pending)⟩).word = tail
      rw [allowed]
      exact rest

end ComplexityOfGenerators.Examples.HAMPATH.Native
