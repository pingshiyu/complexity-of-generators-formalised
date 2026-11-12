import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixDeleteCodec

/-! Insertion in the canonical adjacency matrix is literal row and column
insertion. Existing cells retain their order; only incident-edge bits are new. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

set_option backward.isDefEq.respectTransparency false

theorem contract_bound {size position index : ℕ} (positionBound : position ≤ size)
    (indexBound : index < size+1) (different : index ≠ position) : contract position index < size := by
  unfold contract
  split <;> omega

theorem insertIdx_getElem_other {A : Type} (word : List A) (position : ℕ) (letter : A)
    (fits : position ≤ word.length) (index : ℕ) (inside : index < word.length+1) (different : index ≠ position) :
    (word.insertIdx position letter)[index]'(by rw [List.length_insertIdx_of_le_length fits]; exact inside) =
      word[contract position index]'(contract_bound fits inside different) := by
  by_cases earlier : index < position
  · rw [List.getElem_insertIdx_of_lt earlier]
    simp only [contract,ite_eq_left earlier]
  · have later : position < index := by omega
    rw [List.getElem_insertIdx_of_gt later]
    simp only [contract,ite_eq_right earlier]

/-- A row receives its incoming edge at the new column; then the outgoing
row is inserted at the same ordered position. -/
def insertMatrixRows {A : Type} (rows : List (List A)) (position : ℕ)
    (incoming : ℕ → A) (newRow : List A) : List (List A) :=
  (rows.mapIdx (fun index row => row.insertIdx position (incoming index))).insertIdx position newRow

@[simp] theorem insertMatrixRows_length {A : Type} (rows : List (List A)) (position : ℕ)
    (incoming : ℕ → A) (newRow : List A) (fits : position ≤ rows.length) :
    (insertMatrixRows rows position incoming newRow).length = rows.length+1 := by
  rw [insertMatrixRows,List.length_insertIdx_of_le_length (by simpa using fits),List.length_mapIdx]

theorem insertMatrixRows_row {A : Type} (rows : List (List A)) (position : ℕ)
    (incoming : ℕ → A) (newRow : List A) (fits : position ≤ rows.length)
    (index : ℕ) (inside : index < rows.length+1) :
    (insertMatrixRows rows position incoming newRow)[index]'(by rw [insertMatrixRows_length rows position incoming newRow fits]; exact inside) =
      if same : index = position then newRow else
        (rows[contract position index]'(contract_bound fits inside same)).insertIdx position (incoming (contract position index)) := by
  by_cases same : index = position
  · subst index
    simp [insertMatrixRows]
  · simp only [insertMatrixRows]
    rw [insertIdx_getElem_other _ _ _ (by simpa using fits) index (by simpa using inside) same,
      List.getElem_mapIdx]
    simp only [dif_neg same]

def insertedSymbolRows (graph : Graph) (position : ℕ) (incoming outgoing : ℕ → Bool) : List (List Symbol) :=
  insertMatrixRows (graphSymbolRows graph) position (fun vertex => Symbol.bit (incoming vertex))
    (((List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))).insertIdx position (.bit false))

theorem graphSymbolRows_row (graph : Graph) (vertex : ℕ) (inside : vertex < graph.size) :
    (graphSymbolRows graph)[vertex]'(by simpa using inside) =
      (List.range graph.size).map (fun next => Symbol.bit (graph.edge vertex next)) := by
  simp [graphSymbolRows,graphRows,List.getElem_map,inside,List.map_map,Function.comp_def]

/-- The pure row/column insertion algorithm is exactly graph insertion,
including both the old and new diagonal cells. -/
theorem graphSymbolRows_insert (graph : Graph) (position : ℕ) (fits : position ≤ graph.size)
    (incoming outgoing : ℕ → Bool) :
    graphSymbolRows (graph.insert position incoming outgoing) = insertedSymbolRows graph position incoming outgoing := by
  apply List.ext_getElem
  · simp [insertedSymbolRows,Graph.insert,fits]
  · intro vertex left right
    have vertexBound : vertex < graph.size+1 := by simpa [Graph.insert] using left
    rw [graphSymbolRows_row _ vertex vertexBound]
    simp only [insertedSymbolRows]
    rw [insertMatrixRows_row _ position _ _ (by simpa using fits) vertex (by simpa using vertexBound)]
    by_cases newVertex : vertex = position
    · subst vertex
      simp only [dite_true]
      apply List.ext_getElem
      · simp [Graph.insert,List.length_insertIdx,fits]
      · intro next first second
        have nextBound : next < graph.size+1 := by simpa [Graph.insert] using first
        rw [List.getElem_map,List.getElem_range]
        by_cases diagonal : next = position
        · subst next
          rw [List.getElem_insertIdx_self]
          simp [(graph.insert position incoming outgoing).loopFree]
        · rw [insertIdx_getElem_other ((List.range graph.size).map (fun vertex => Symbol.bit (outgoing vertex))) position (.bit false) (by simpa using fits) next (by simpa using nextBound) diagonal,
            List.getElem_map,List.getElem_range]
          have different : position ≠ next := Ne.symm diagonal
          simp [Graph.insert,fits,show next ≤ graph.size by omega,different,contract]
    · simp only [dif_neg newVertex]
      have oldVertex : contract position vertex < graph.size := contract_bound fits vertexBound newVertex
      rw [graphSymbolRows_row graph _ oldVertex]
      apply List.ext_getElem
      · simp [Graph.insert,List.length_insertIdx,fits]
      · intro next first second
        have nextBound : next < graph.size+1 := by simpa [Graph.insert] using first
        rw [List.getElem_map,List.getElem_range]
        by_cases newColumn : next = position
        · subst next
          rw [List.getElem_insertIdx_self]
          simp [Graph.insert,show vertex ≤ graph.size by omega,fits,newVertex]
        · rw [insertIdx_getElem_other ((List.range graph.size).map (fun next => Symbol.bit (graph.edge (contract position vertex) next))) position (.bit (incoming (contract position vertex))) (by simpa using fits) next (by simpa using nextBound) newColumn,
            List.getElem_map,List.getElem_range]
          by_cases diagonal : vertex = next
          · subst next
            simp [(graph.insert position incoming outgoing).loopFree,graph.loopFree]
          · simp [Graph.insert,show vertex ≤ graph.size by omega,show next ≤ graph.size by omega,diagonal,newVertex,newColumn]

theorem matrixWord_insert (graph : Graph) (position : ℕ) (fits : position ≤ graph.size)
    (incoming outgoing : ℕ → Bool) :
    (graph.insert position incoming outgoing).matrixWord = (insertedSymbolRows graph position incoming outgoing).flatten := by
  rw [← graphSymbolRows_flatten,graphSymbolRows_insert graph position fits]

end ComplexityOfGenerators.Examples.HAMPATH.Native
