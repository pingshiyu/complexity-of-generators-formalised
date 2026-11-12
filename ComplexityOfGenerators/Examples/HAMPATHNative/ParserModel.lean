import ComplexityOfGenerators.Examples.HAMPATHNative.Parser
import ComplexityOfGenerators.Examples.HAMPATHNative.RowModel
import ComplexityOfGenerators.Examples.HAMPATHNative.StartModel
import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixCodec

/-! The native streaming syntax checker accepts exactly the validated graph
encodings recognized by the executable decoder. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.Native

set_option backward.isDefEq.respectTransparency false

theorem headerState_sound (word : List Symbol) (valid : (headerState word).valid = true) :
    (headerState word).row = 0 ∧
      word = List.replicate (headerSize word) (Symbol.bit true) ++ Symbol.separator :: (headerState word).word := by
  cases rest : word.dropWhile keepHeader with
  | nil => simp [headerState, rest] at valid
  | cons head tail =>
      cases head with
      | bit value => simp [headerState, rest] at valid
      | separator =>
          constructor
          · simp [headerState, rest]
          · have wordPrefix : word = word.takeWhile keepHeader ++ word.dropWhile keepHeader := List.takeWhile_append_dropWhile.symm
            simpa only [header_replicate, rest, headerState, List.head?_cons, ite_true, List.tail_cons] using wordPrefix

theorem separator_sound (state : RowState) (valid : (separator state).valid = true) :
    state.valid = true ∧ state.word = Symbol.separator :: (separator state).word := by
  by_cases found : state.word.head? = some Symbol.separator
  · constructor
    · simpa only [separator, ite_eq_left found] using valid
    · cases word : state.word with
      | nil => simp [word] at found
      | cons head tail =>
          have same : head = Symbol.separator := by simpa only [word, List.head?_cons, Option.some.injEq] using found
          simp [separator, found, word, same]
  · simp [separator, found] at valid

theorem canonical_header_size (k : ℕ) (tail : List Symbol) :
    headerSize (List.replicate k (Symbol.bit true) ++ Symbol.separator :: tail) = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      simpa only [headerSize, List.replicate_succ, List.cons_append, List.takeWhile_cons,
        keepHeader, beq_self_eq_true, ite_true, List.length_cons, Nat.add_left_cancel_iff] using congrArg Nat.succ ih

theorem canonical_header_state (k : ℕ) (tail : List Symbol) :
    headerState (List.replicate k (Symbol.bit true) ++ Symbol.separator :: tail) = ⟨tail, 0, true⟩ := by
  have remaining : (List.replicate k (Symbol.bit true) ++ Symbol.separator :: tail).dropWhile keepHeader = Symbol.separator :: tail := by
    induction k with
    | zero => rfl
    | succ k ih => simpa only [List.replicate_succ, List.cons_append, List.dropWhile_cons,
        keepHeader, beq_self_eq_true, ite_true] using ih
  simp only [headerState, remaining, List.head?_cons, ite_true, List.tail_cons]

theorem range_oneHot (size start : ℕ) (inside : start < size) :
    (List.range size).map (fun v => Symbol.bit (decide (v = start))) = oneHot size start := by
  induction start generalizing size with
  | zero =>
      cases size with
      | zero => omega
      | succ size =>
          simp [List.range_succ_eq_map, oneHot, List.map_map, Function.comp_def, List.map_const']
  | succ start ih =>
      cases size with
      | zero => omega
      | succ size =>
          have rest := ih size (by omega)
          simpa [List.range_succ_eq_map, oneHot, List.map_map, Function.comp_def,
            List.replicate_succ, Nat.add_sub_add_right] using congrArg (Symbol.bit false :: ·) rest

def graphRows (graph : Graph) : List (List Bool) :=
  (List.range graph.size).map (fun v => (List.range graph.size).map (graph.edge v))

@[simp] theorem graphRows_length (graph : Graph) : (graphRows graph).length = graph.size := by simp [graphRows]

theorem graphRows_rectangular (graph : Graph) : Rectangular graph.size (graphRows graph) := by
  intro row member
  obtain ⟨v, _, rfl⟩ := List.mem_map.mp member
  simp

theorem graphRows_diagonal (graph : Graph) :
    ∀ (i : ℕ) (row : List Bool), (graphRows graph)[i]? = some row → row[i]? = some false := by
  intro i row found
  obtain ⟨inside, equal⟩ := List.getElem?_eq_some_iff.mp found
  have bound : i < graph.size := by simpa using inside
  have rowEq : row = (List.range graph.size).map (graph.edge i) := by
    simpa [graphRows] using equal.symm
  rw [rowEq, List.getElem?_map, List.getElem?_range bound]
  simp [graph.loopFree]

theorem graphRows_diagonals (graph : Graph) : Diagonals 0 graph.size (graphRows graph) := by
  intro i row found _
  simpa only [Nat.zero_add] using graphRows_diagonal graph i row found

theorem graphRows_matrixWord (graph : Graph) : (graphRows graph).flatten.map Symbol.bit = graph.matrixWord := by
  simp only [graphRows, List.map_flatten, List.map_map, List.flatten_eq_flatMap, List.flatMap_map, List.map_flatMap,
    Function.comp_def, id_eq, Graph.matrixWord]

theorem headerSize_encode (graph : Graph) (start : ℕ) : headerSize (graph.encode start) = graph.size := by
  simpa only [Graph.encode, Graph.matrixWord, List.append_assoc, List.cons_append, List.nil_append] using
    canonical_header_size graph.size (graph.matrixWord ++ Symbol.separator ::
      (List.range graph.size).map (fun v => Symbol.bit (decide (v = start))))

theorem headerState_encode (graph : Graph) (start : ℕ) :
    headerState (graph.encode start) =
      ⟨graph.matrixWord ++ Symbol.separator :: (List.range graph.size).map (fun v => Symbol.bit (decide (v = start))), 0, true⟩ := by
  simpa only [Graph.encode, Graph.matrixWord, List.append_assoc, List.cons_append, List.nil_append] using
    canonical_header_state graph.size (graph.matrixWord ++ Symbol.separator ::
      (List.range graph.size).map (fun v => Symbol.bit (decide (v = start))))


theorem wellFormed_sound (word : List Symbol) (accepted : wellFormed word = true) :
    (decode word).isSome := by
  have flags : (parsedState word).valid = true ∧ (parsedState word).seen = true ∧ (parsedState word).word = [] := by
    simpa only [wellFormed, Bool.and_eq_true, List.isEmpty_iff, and_assoc] using accepted
  have afterValid : (afterMatrix word).valid = true :=
    startIterate_initialValid _ _ flags.1
  have matrixGood := separator_sound (matrixState word) afterValid
  have headerValid : (headerState word).valid = true :=
    rowIterate_initialValid _ _ _ matrixGood.1
  have headerGood := headerState_sound word headerValid
  obtain ⟨rows, rowCount, rectangle, diagonals, matrixWord⟩ :=
    rowIterate_sound (headerSize word) (headerSize word) (headerState word) matrixGood.1
  change (headerState word).word = rows.flatten.map Symbol.bit ++ (matrixState word).word at matrixWord
  have diagonal : ∀ (i : ℕ) (row : List Bool), rows[i]? = some row → row[i]? = some false := by
    intro i row found
    have index := (List.getElem?_eq_some_iff.mp found).1
    have inside : (headerState word).row + i < headerSize word := by rw [headerGood.1]; omega
    simpa only [headerGood.1, Nat.zero_add] using diagonals i row found inside
  have parsedEq : parsedState word =
      startStep^[headerSize word] ⟨(afterMatrix word).word, 0, false, true⟩ := by
    simp only [parsedState, afterValid]
  have parsedValid : (startStep^[headerSize word] ⟨(afterMatrix word).word, 0, false, true⟩).valid = true := by
    rw [← parsedEq]
    exact flags.1
  have parsedSeen : (startStep^[headerSize word] ⟨(afterMatrix word).word, 0, false, true⟩).seen = true := by
    rw [← parsedEq]
    exact flags.2.1
  obtain ⟨start, inside, startWord, _⟩ := startIterate_sound (headerSize word) (afterMatrix word).word 0 parsedValid parsedSeen
  rw [← parsedEq, flags.2.2] at startWord
  have startCanonical : (afterMatrix word).word = oneHot (headerSize word) start := by
    simpa only [oneHot, List.append_nil] using startWord
  have fullWord : word =
      List.replicate (headerSize word) (Symbol.bit true) ++ [Symbol.separator] ++ rows.flatten.map Symbol.bit ++ [Symbol.separator] ++
        (List.range (headerSize word)).map (fun v => Symbol.bit (decide (v = start))) := by
    have reconstructedWord := headerGood.2
    rw [matrixWord, matrixGood.2] at reconstructedWord
    change word = List.replicate (headerSize word) (Symbol.bit true) ++ Symbol.separator ::
      (rows.flatten.map Symbol.bit ++ Symbol.separator :: (afterMatrix word).word) at reconstructedWord
    rw [startCanonical, ← range_oneHot _ _ inside] at reconstructedWord
    simpa only [List.append_assoc, List.cons_append, List.nil_append] using reconstructedWord
  apply (decode_isSome_iff_encoding word).mpr
  refine ⟨Graph.fromMatrix (headerSize word) (rows.flatten.map Symbol.bit), start, inside, ?_⟩
  exact (fromMatrix_encode_rows rows (headerSize word) start rowCount rectangle diagonal).trans fullWord.symm

theorem parsedState_encode (graph : Graph) (start : ℕ) (inside : start < graph.size) :
    parsedState (graph.encode start) = ⟨[], start, true, true⟩ := by
  let tail := Symbol.separator :: (List.range graph.size).map (fun v => Symbol.bit (decide (v = start)))
  have scanned := rowIterate_complete graph.size (graphRows graph) tail 0
    (graphRows_rectangular graph) (graphRows_diagonals graph)
  dsimp only at scanned
  rw [graphRows_length, graphRows_matrixWord] at scanned
  have matrixEq : matrixState (graph.encode start) =
      (rowStep graph.size)^[graph.size] ⟨graph.matrixWord ++ tail, 0, true⟩ := by
    rw [matrixState, headerSize_encode, headerState_encode]
  rw [← matrixEq] at scanned
  have afterGood : (afterMatrix (graph.encode start)).valid = true ∧
      (afterMatrix (graph.encode start)).word =
        (List.range graph.size).map (fun v => Symbol.bit (decide (v = start))) := by
    simp only [afterMatrix, separator, scanned.2, tail, List.head?_cons, ite_true, List.tail_cons]
    exact ⟨scanned.1, by trivial⟩
  rw [parsedState, headerSize_encode, afterGood.1, afterGood.2, range_oneHot _ _ inside]
  simpa only [List.append_nil] using startIterate_complete graph.size start inside []

theorem wellFormed_encode (graph : Graph) (start : ℕ) (inside : start < graph.size) :
    wellFormed (graph.encode start) = true := by
  simp [wellFormed, parsedState_encode graph start inside]

/-- The finite native syntax parser agrees with the independently executable
validated decoder on every input word, including malformed inputs. -/
theorem wellFormed_iff_decode (word : List Symbol) : wellFormed word = true ↔ (decode word).isSome := by
  constructor
  · exact wellFormed_sound word
  · intro decoded
    obtain ⟨graph, start, inside, encoded⟩ := (decode_isSome_iff_encoding word).mp decoded
    rw [← encoded]
    exact wellFormed_encode graph start inside

end ComplexityOfGenerators.Examples.HAMPATH.Native
