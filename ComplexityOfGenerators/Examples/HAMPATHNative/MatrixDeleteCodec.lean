import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel

/-! Deleting a vertex removes its adjacency row and column in the canonical
word representation. The relabelling is precisely the order-preserving one
used by the graph operation. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

set_option backward.isDefEq.respectTransparency false

private theorem eraseIdx_map_eq {A B : Type} (f : A → B) (word : List A) (position : ℕ) :
    (word.map f).eraseIdx position = (word.eraseIdx position).map f := by
  induction word generalizing position with
  | nil => simp
  | cons letter rest ih => cases position <;> simp [ih]

theorem range_eraseIdx (size start : ℕ) (inside : start < size) :
    (List.range size).eraseIdx start = (List.range (size - 1)).map (expand start) := by
  apply List.ext_getElem
  · simp [List.length_eraseIdx_of_lt (l := List.range size) (i := start) (by simpa using inside)]
  · intro index left right
    rw [List.getElem_eraseIdx]
    simp only [List.getElem_map, List.getElem_range, expand]
    split <;> rfl

/-- The row-list implementation of removing a vertex agrees with the graph's
ordered relabelling, before any flattening or symbol encoding. -/
theorem graphRows_delete (graph : Graph) (start : ℕ) (inside : start < graph.size) :
    graphRows (graph.delete start) =
      ((graphRows graph).eraseIdx start).map (fun row => row.eraseIdx start) := by
  rw [graphRows, graphRows, eraseIdx_map_eq, range_eraseIdx graph.size start inside]
  simp only [Graph.delete, List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro vertex member
  have row : vertex < graph.size - 1 := List.mem_range.mp member
  rw [eraseIdx_map_eq, range_eraseIdx graph.size start inside]
  simp only [List.map_map, Function.comp_def]
  apply List.map_congr_left
  intro column member
  have col : column < graph.size - 1 := List.mem_range.mp member
  simp [row, col]

theorem matrixWord_delete (graph : Graph) (start : ℕ) (inside : start < graph.size) :
    (graph.delete start).matrixWord =
      (((graphRows graph).eraseIdx start).map (fun row => row.eraseIdx start)).flatten.map Symbol.bit := by
  rw [← graphRows_matrixWord, graphRows_delete graph start inside]

def graphSymbolRows (graph : Graph) : List (List Symbol) :=
  (graphRows graph).map (List.map Symbol.bit)

@[simp] theorem graphSymbolRows_length (graph : Graph) :
    (graphSymbolRows graph).length = graph.size := by simp [graphSymbolRows]

theorem graphSymbolRows_rectangular (graph : Graph) :
    ∀ row ∈ graphSymbolRows graph, row.length = graph.size := by
  intro row member
  change row ∈ (graphRows graph).map (List.map Symbol.bit) at member
  obtain ⟨bits, bitsMember, rfl⟩ := List.mem_map.mp member
  simpa only [List.length_map] using graphRows_rectangular graph bits bitsMember

theorem graphSymbolRows_flatten (graph : Graph) :
    (graphSymbolRows graph).flatten = graph.matrixWord := by
  rw [graphSymbolRows, ← List.map_flatten]
  exact graphRows_matrixWord graph

theorem matrixWord_delete_symbol_rows (graph : Graph) (start : ℕ) (inside : start < graph.size) :
    (graph.delete start).matrixWord =
      (((graphSymbolRows graph).eraseIdx start).map (fun row => row.eraseIdx start)).flatten := by
  rw [matrixWord_delete graph start inside, graphSymbolRows, eraseIdx_map_eq]
  simp only [List.map_map, Function.comp_def, eraseIdx_map_eq, List.map_flatten]

end ComplexityOfGenerators.Examples.HAMPATH.Native
