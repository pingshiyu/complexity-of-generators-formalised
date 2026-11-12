import ComplexityOfGenerators.Examples.HAMPATHNative.Rows

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

def Rectangular (size : ℕ) (rows : List (List Bool)) : Prop := ∀ row ∈ rows, row.length = size

def Diagonals (offset size : ℕ) (rows : List (List Bool)) : Prop :=
  ∀ i row, rows[i]? = some row → offset + i < size → row[offset + i]? = some false

theorem rowStep_invalid (size : ℕ) (state : RowState) (invalid : state.valid = false) :
    (rowStep size state).valid = false :=
  cellIterate_invalid ⟨state.word, state.row, true, state.valid⟩ invalid size

theorem rowIterate_invalid (size count : ℕ) (state : RowState) (invalid : state.valid = false) :
    ((rowStep size)^[count] state).valid = false := by
  induction count generalizing state with
  | zero => exact invalid
  | succ count ih =>
      rw [Function.iterate_succ_apply]
      exact ih (rowStep size state) (rowStep_invalid size state invalid)

theorem rowIterate_initialValid (size count : ℕ) (state : RowState)
    (accepted : ((rowStep size)^[count] state).valid = true) : state.valid = true := by
  cases valid : state.valid with
  | true => rfl
  | false => rw [rowIterate_invalid size count state valid] at accepted; cases accepted

theorem rowIterate_number (size count : ℕ) (state : RowState) :
    ((rowStep size)^[count] state).row = state.row + count := by
  induction count generalizing state with
  | zero => simp
  | succ count ih => rw [Function.iterate_succ_apply, ih]; simp [rowStep]; omega

/-- Successful native matrix scans consume a rectangular Boolean matrix
whose distinguished diagonal entries are all false. -/
theorem rowIterate_sound (size count : ℕ) (state : RowState)
    (accepted : ((rowStep size)^[count] state).valid = true) :
    ∃ matrix : List (List Bool), matrix.length = count ∧ Rectangular size matrix ∧
      Diagonals state.row size matrix ∧
      state.word = matrix.flatten.map Symbol.bit ++ ((rowStep size)^[count] state).word := by
  induction count generalizing state with
  | zero => exact ⟨[], rfl, by simp [Rectangular], by simp [Diagonals], by simp⟩
  | succ count ih =>
      rw [Function.iterate_succ_apply] at accepted ⊢
      have first := rowIterate_initialValid size count (rowStep size state) accepted
      change (cellStep^[size] ⟨state.word, state.row, true, state.valid⟩).valid = true at first
      obtain ⟨row, length, firstWord, diagonal⟩ := cellIterate_sound size _ first
      obtain ⟨matrix, rows, rectangle, diagonals, tailWord⟩ := ih (rowStep size state) accepted
      refine ⟨row :: matrix, by simp [rows], ?_, ?_, ?_⟩
      · intro r member
        rcases List.mem_cons.mp member with rfl | member
        · exact length
        · exact rectangle r member
      · intro i r member inside
        cases i with
        | zero =>
            have same : row = r := by simpa using member
            subst r
            exact diagonal rfl (by simpa using inside)
        | succ i =>
            have found : matrix[i]? = some r := by simpa using member
            have atNext := diagonals i r found (by change state.row + 1 + i < size; omega)
            simpa [rowStep, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using atNext
      · change state.word = (row ++ matrix.flatten).map Symbol.bit ++ _
        rw [List.map_append, List.append_assoc]
        apply firstWord.trans
        congr 1

theorem rowIterate_complete (size : ℕ) (matrix : List (List Bool)) (tail : List Symbol) (offset : ℕ)
    (rectangle : Rectangular size matrix) (diagonals : Diagonals offset size matrix) :
    let result := (rowStep size)^[matrix.length] ⟨matrix.flatten.map Symbol.bit ++ tail, offset, true⟩
    result.valid = true ∧ result.word = tail := by
  induction matrix generalizing offset with
  | nil => simp
  | cons row matrix ih =>
      have length := rectangle row (by simp)
      have firstGood : true = true → offset < row.length → row[offset]? = some false := by
        intro _ inside
        exact diagonals 0 row (by simp) (by simpa [length] using inside)
      have first := cellIterate_complete row (matrix.flatten.map Symbol.bit ++ tail) offset true firstGood
      rw [length] at first
      have remaining : Rectangular size matrix := by intro r hr; exact rectangle r (by simp [hr])
      have remainingDiagonal : Diagonals (offset + 1) size matrix := by
        intro i r member inside
        have found := diagonals (i + 1) r (by simpa using member) (by omega)
        simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using found
      have rest := ih (offset + 1) remaining remainingDiagonal
      rw [List.length_cons, Function.iterate_succ_apply]
      change ((rowStep size)^[matrix.length]
        ⟨(cellStep^[size] ⟨(row ++ matrix.flatten).map Symbol.bit ++ tail, offset, true, true⟩).word,
          offset + 1,
          (cellStep^[size] ⟨(row ++ matrix.flatten).map Symbol.bit ++ tail, offset, true, true⟩).valid⟩).valid = true ∧
        ((rowStep size)^[matrix.length]
          ⟨(cellStep^[size] ⟨(row ++ matrix.flatten).map Symbol.bit ++ tail, offset, true, true⟩).word,
            offset + 1,
            (cellStep^[size] ⟨(row ++ matrix.flatten).map Symbol.bit ++ tail, offset, true, true⟩).valid⟩).word = tail
      simp only [List.map_append, List.append_assoc]
      rw [first.1, first.2]
      exact rest

end ComplexityOfGenerators.Examples.HAMPATH.Native
