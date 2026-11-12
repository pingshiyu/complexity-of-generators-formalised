import ComplexityOfGenerators.Examples.HAMPATHParser

/-! Reconstructing the canonical graph matrix from successful rectangular
Boolean rows. The diagonal check exactly matches loop-free graph encoding. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

set_option backward.isDefEq.respectTransparency false

theorem rectangular_flatten_length {A : Type} (rows : List (List A)) (width : ℕ)
    (lengths : ∀ row ∈ rows, row.length = width) : rows.flatten.length = rows.length * width := by
  induction rows with
  | nil => simp
  | cons row rest ih =>
    have head := lengths row (by simp)
    have tail := ih (by intro r member; exact lengths r (by simp [member]))
    simp only [List.flatten_cons, List.length_append, List.length_cons, head, tail, Nat.succ_mul]
    omega

theorem matrix_rows_lookup (rows : List (List Bool)) (k : ℕ)
    (rowCount : rows.length = k) (lengths : ∀ row ∈ rows, row.length = k)
    (v w : ℕ) (row : v < k) (column : w < k) :
    (rows.flatten.map Symbol.bit)[v*k+w]? =
      some (Symbol.bit ((rows[v]'(by omega))[w]'(by rw [lengths _ (List.getElem_mem _)]; exact column))) := by
  have inside : v < rows.length := by omega
  have width := lengths (rows[v]'inside) (List.getElem_mem _)
  have cellInside : w < (rows[v]'inside).length := by omega
  rw [List.getElem?_map, block_lookup rows k v w lengths inside column,
    List.getElem?_eq_getElem cellInside]
  rfl

theorem fromMatrix_rows_lookup (rows : List (List Bool)) (k : ℕ)
    (rowCount : rows.length = k) (lengths : ∀ row ∈ rows, row.length = k)
    (diagonal : ∀ (i : ℕ) (row : List Bool), rows[i]? = some row → row[i]? = some false)
    (v w : ℕ) (row : v < k) (column : w < k) :
    some (Symbol.bit ((Graph.fromMatrix k (rows.flatten.map Symbol.bit)).edge v w)) =
      (rows.flatten.map Symbol.bit)[v*k+w]? := by
  have inside : v < rows.length := by omega
  have rowWidth := lengths (rows[v]'inside) (List.getElem_mem _)
  have cellInside : w < (rows[v]'inside).length := by omega
  have lookup := matrix_rows_lookup rows k rowCount lengths v w row column
  by_cases different : v ≠ w
  · rw [lookup]
    simp only [Graph.fromMatrix, ite_eq_left (show v < k ∧ w < k ∧ v ≠ w from ⟨row, column, different⟩),
      lookup, Option.map_some, readBit, Option.getD_some]
  · have same : v = w := by simpa using different
    subst w
    have falseCell := diagonal v (rows[v]'inside) (List.getElem?_eq_getElem inside)
    rw [List.getElem?_eq_getElem cellInside] at falseCell
    have valueFalse := Option.some.inj falseCell
    rw [lookup, valueFalse]
    simp [Graph.fromMatrix]

/-- Every successful square row model is exactly the canonical adjacency
matrix of its reconstructed graph, including the empty square. -/
theorem fromMatrix_matrixWord_rows (rows : List (List Bool)) (k : ℕ)
    (rowCount : rows.length = k) (lengths : ∀ row ∈ rows, row.length = k)
    (diagonal : ∀ (i : ℕ) (row : List Bool), rows[i]? = some row → row[i]? = some false) :
    (Graph.fromMatrix k (rows.flatten.map Symbol.bit)).matrixWord = rows.flatten.map Symbol.bit := by
  have matrixLength : (rows.flatten.map Symbol.bit).length = k*k := by
    rw [List.length_map, rectangular_flatten_length rows k lengths, rowCount]
  apply List.ext_getElem?
  intro index
  by_cases inside : index < k*k
  · have positive : 0 < k := by
      by_contra absent
      have zero : k = 0 := by omega
      rw [zero] at inside
      omega
    have row : index / k < k := (Nat.div_lt_iff_lt_mul positive).mpr inside
    have column : index % k < k := Nat.mod_lt _ positive
    have address : (index / k)*k + index%k = index := by
      simpa only [Nat.mul_comm] using Nat.div_add_mod index k
    have canonical := Graph.matrixWord_lookup (Graph.fromMatrix k (rows.flatten.map Symbol.bit))
      (index/k) (index%k) row column
    have reconstructed := fromMatrix_rows_lookup rows k rowCount lengths diagonal (index/k) (index%k) row column
    change (Graph.fromMatrix k (rows.flatten.map Symbol.bit)).matrixWord[index/k*k + index%k]? = _ at canonical
    rw [address] at canonical reconstructed
    exact canonical.trans reconstructed
  · rw [List.getElem?_eq_none (by
      rw [Graph.matrixWord_length]
      change k*k ≤ index
      omega),
      List.getElem?_eq_none (by rw [matrixLength]; omega)]

theorem decode_isSome_iff_encoding (word : List Symbol) :
    (decode word).isSome ↔ ∃ graph : Graph, ∃ start, start < graph.size ∧ graph.encode start = word := by
  constructor
  · intro accepted
    cases output : decode word with
    | none => simp [output] at accepted
    | some pair => exact ⟨pair.1, pair.2, decode_sound output⟩
  · rintro ⟨graph, start, inside, rfl⟩
    rw [decode_encode graph start inside]
    rfl


theorem fromMatrix_encode_rows (rows : List (List Bool)) (k start : ℕ)
    (rowCount : rows.length = k) (lengths : ∀ row ∈ rows, row.length = k)
    (diagonal : ∀ (i : ℕ) (row : List Bool), rows[i]? = some row → row[i]? = some false) :
    (Graph.fromMatrix k (rows.flatten.map Symbol.bit)).encode start =
      List.replicate k (.bit true) ++ [.separator] ++ rows.flatten.map Symbol.bit ++ [.separator] ++
        (List.range k).map (fun v => Symbol.bit (decide (v = start))) := by
  change List.replicate k (.bit true) ++ [.separator] ++
    (Graph.fromMatrix k (rows.flatten.map Symbol.bit)).matrixWord ++ [.separator] ++
      (List.range k).map (fun v => Symbol.bit (decide (v = start))) = _
  rw [fromMatrix_matrixWord_rows rows k rowCount lengths diagonal]

theorem decode_rows (rows : List (List Bool)) (k start : ℕ)
    (rowCount : rows.length = k) (lengths : ∀ row ∈ rows, row.length = k)
    (diagonal : ∀ (i : ℕ) (row : List Bool), rows[i]? = some row → row[i]? = some false)
    (inside : start < k) :
    decode (List.replicate k (.bit true) ++ [.separator] ++ rows.flatten.map Symbol.bit ++ [.separator] ++
      (List.range k).map (fun v => Symbol.bit (decide (v = start)))) =
        some (Graph.fromMatrix k (rows.flatten.map Symbol.bit), start) := by
  rw [← fromMatrix_encode_rows rows k start rowCount lengths diagonal]
  exact decode_encode _ start inside

end ComplexityOfGenerators.Examples.HAMPATH.Native
