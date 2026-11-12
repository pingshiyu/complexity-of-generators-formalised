import ComplexityOfGenerators.Examples.HAMPATHCodec

/-! An executable, validated decoder for the adjacency-matrix word encoding.
Re-encoding validation rejects malformed headers, matrices and start fields. -/

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

theorem block_lookup {A : Type} (rows : List (List A)) (width i j : ℕ)
    (lengths : ∀ row ∈ rows, row.length = width) (inside : i < rows.length) (column : j < width) :
    rows.flatten[i * width + j]? = rows[i][j]? := by
  induction rows generalizing i with
  | nil => simp at inside
  | cons row rest ih =>
    have rowLength := lengths row (by simp)
    cases i with
    | zero =>
      simp only [Nat.zero_mul, Nat.zero_add, List.flatten_cons, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by omega)]
    | succ i =>
      have tailLength : i < rest.length := by simpa using inside
      have tail := ih i (by intro r hr; exact lengths r (by simp [hr])) tailLength
      simp only [List.flatten_cons, List.getElem_cons_succ]
      have part : width ≤ (i + 1) * width + j := by rw [Nat.succ_mul]; omega
      rw [List.getElem?_append_right (by rw [rowLength]; exact part), rowLength]
      have offset : (i + 1) * width + j - width = i * width + j := by rw [Nat.succ_mul]; omega
      simpa only [offset] using tail

private theorem flatMap_eq_flatten_map {A B : Type} (xs : List A) (f : A → List B) :
    xs.flatMap f = (xs.map f).flatten := by
  induction xs with
  | nil => rfl
  | cons x rest ih => simpa only [List.flatMap_cons, List.map_cons, List.flatten_cons, ih]

def Graph.matrixWord (G : Graph) : List Symbol :=
  (List.range G.size).flatMap (fun v =>
    (List.range G.size).map (fun w => Symbol.bit (G.edge v w)))

@[simp] theorem Graph.matrixWord_length (G : Graph) :
    G.matrixWord.length = G.size * G.size := by simp [matrixWord, List.length_flatMap]

theorem Graph.matrixWord_lookup (G : Graph) (v w : ℕ) (row : v < G.size) (column : w < G.size) :
    G.matrixWord[v * G.size + w]? = some (.bit (G.edge v w)) := by
  have lookup := block_lookup
    ((List.range G.size).map (fun v => (List.range G.size).map (fun w => Symbol.bit (G.edge v w))))
    G.size v w (by simp) (by simpa using row) column
  simpa [Graph.matrixWord, ← flatMap_eq_flatten_map, List.getElem_map, List.getElem_range,
    List.getElem?_map, List.getElem?_range column] using lookup

def readBit : Symbol → Bool
  | .bit value => value
  | .separator => false

/-- The graph reconstructed from a finite matrix block; invalid diagonal or
symbol data is caught by the whole-word validation below. -/
def Graph.fromMatrix (size : ℕ) (matrix : List Symbol) : Graph where
  size := size
  edge := fun v w => if v < size ∧ w < size ∧ v ≠ w then
    (matrix[v * size + w]?).map readBit |>.getD false else false
  outside := by
    intro v w outside
    rcases outside with left | right
    · simp [show ¬ v < size by omega]
    · simp [show ¬ w < size by omega]
  loopFree := by intro v; simp

@[simp] theorem Graph.fromMatrix_encode (G : Graph) : Graph.fromMatrix G.size G.matrixWord = G := by
  apply Graph.ext (Graph.fromMatrix G.size G.matrixWord) G rfl
  intro v w
  by_cases row : v < G.size
  · by_cases column : w < G.size
    · by_cases different : v ≠ w
      · simp [fromMatrix, row, column, different, G.matrixWord_lookup v w row column, readBit]
      · have same : v = w := by simpa using different
        subst w
        simp [fromMatrix, G.loopFree]
    · simp [fromMatrix, column, G.outside v w (Or.inr (by omega))]
  · simp [fromMatrix, row, G.outside v w (Or.inl (by omega))]

def decode (word : List Symbol) : Option (Graph × ℕ) :=
  let size := (word.takeWhile (· == .bit true)).length
  let matrix := (word.drop (size + 1)).take (size * size)
  let tail := word.drop (size + 1 + size * size + 1)
  let start := tail.findIdx (· == .bit true)
  let graph := Graph.fromMatrix size matrix
  if start < size ∧ graph.encode start = word then some (graph, start) else none

theorem decode_sound {word : List Symbol} {G : Graph} {start : ℕ}
    (decoded : decode word = some (G, start)) : start < G.size ∧ G.encode start = word := by
  dsimp only [decode] at decoded
  split at decoded
  · rename_i valid
    have equal := Option.some.inj decoded
    cases equal
    exact valid
  · simp at decoded


theorem Graph.matrixWord_of_encoding (G : Graph) (start : ℕ) :
    ((G.encode start).drop (G.size + 1)).take (G.size * G.size) = G.matrixWord := by
  have afterHeader : (G.encode start).drop (G.size + 1) =
      G.matrixWord ++ [Symbol.separator] ++
        (List.range G.size).map (fun v => Symbol.bit (decide (v = start))) := by
    simp [Graph.encode, Graph.matrixWord, List.append_assoc, List.drop_append]
  rw [afterHeader, List.append_assoc, ← G.matrixWord_length, List.take_left]

theorem Graph.startWord_of_encoding (G : Graph) (start : ℕ) :
    (G.encode start).drop (G.size + 1 + G.size * G.size + 1) =
      (List.range G.size).map (fun v => Symbol.bit (decide (v = start))) := by
  change (List.replicate G.size (Symbol.bit true) ++ [Symbol.separator] ++
    G.matrixWord ++ [Symbol.separator] ++
      (List.range G.size).map (fun v => Symbol.bit (decide (v = start)))).drop _ = _
  have prefixLength : (List.replicate G.size (Symbol.bit true) ++ [Symbol.separator] ++
      G.matrixWord ++ [Symbol.separator]).length = G.size + 1 + G.size * G.size + 1 := by simp; omega
  rw [← prefixLength, List.drop_left]

theorem findIdx_onehot (k start : ℕ) (inside : start < k) :
    ((List.range k).map (fun v => Symbol.bit (decide (v = start)))).findIdx (· == .bit true) = start := by
  apply (List.findIdx_eq (by simpa using inside)).mpr
  constructor
  · simp
  · intro j lower
    simp [show j ≠ start by omega]

theorem decode_encode (G : Graph) (start : ℕ) (inside : start < G.size) :
    decode (G.encode start) = some (G, start) := by
  simp only [decode, Graph.header, List.length_replicate,
    Graph.matrixWord_of_encoding, Graph.startWord_of_encoding, findIdx_onehot _ _ inside,
    Graph.fromMatrix_encode, inside, and_self, ite_true]

end ComplexityOfGenerators.Examples.HAMPATH
