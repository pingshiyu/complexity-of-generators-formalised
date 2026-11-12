import ComplexityOfGenerators.Examples.HAMPATHBounds

/-! Recovering the structured graph and start vertex from the paper's concrete
word representation. These injectivity facts support the word-level reduction;
they do not assume a parser or a polynomial native implementation. -/

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

private theorem takeWhile_header (n : ℕ) (tail : List Symbol) :
    (List.replicate n (Symbol.bit true) ++ Symbol.separator :: tail).takeWhile (· == .bit true) =
      List.replicate n (Symbol.bit true) := by
  induction n with
  | zero => simp
  | succ n ih => simp [List.replicate_succ, ih]

theorem Graph.header (G : Graph) (start : ℕ) :
    (G.encode start).takeWhile (· == .bit true) = List.replicate G.size (Symbol.bit true) := by
  simpa [Graph.encode, List.append_assoc] using takeWhile_header G.size
    ((List.range G.size).flatMap (fun v =>
      (List.range G.size).map (fun w => Symbol.bit (G.edge v w))) ++
      [Symbol.separator] ++ (List.range G.size).map (fun v => .bit (decide (v = start))))

theorem Graph.size_of_encode_eq {G H : Graph} {s t : ℕ} (encoded : G.encode s = H.encode t) :
    G.size = H.size := by
  have headers := congrArg (fun word : List Symbol => (word.takeWhile (· == .bit true)).length) encoded
  simpa only [Graph.header, List.length_replicate] using headers

private theorem flatMap_blocks_injective {A B : Type} (xs : List A) (f g : A → List B)
    (lengths : ∀ x ∈ xs, (f x).length = (g x).length)
    (equal : xs.flatMap f = xs.flatMap g) : ∀ x ∈ xs, f x = g x := by
  induction xs with
  | nil => simp
  | cons x rest ih =>
    simp only [List.flatMap_cons] at equal
    obtain ⟨head, tail⟩ := List.append_inj equal (lengths x (by simp))
    intro y member
    rcases List.mem_cons.mp member with rfl | member
    · exact head
    · exact ih (by intro z hz; exact lengths z (by simp [hz])) tail y member

private theorem matrix_length (G : Graph) :
    ((List.range G.size).flatMap (fun v =>
      (List.range G.size).map (fun w => Symbol.bit (G.edge v w)))).length =
      G.size * G.size := by simp [List.length_flatMap]

theorem Graph.matrix_and_start_of_encode_eq {G H : Graph} {s t : ℕ}
    (encoded : G.encode s = H.encode t) :
    (List.range G.size).flatMap (fun v =>
      (List.range G.size).map (fun w => Symbol.bit (G.edge v w))) =
      (List.range H.size).flatMap (fun v =>
        (List.range H.size).map (fun w => Symbol.bit (H.edge v w))) ∧
    (List.range G.size).map (fun v => Symbol.bit (decide (v = s))) =
      (List.range H.size).map (fun v => Symbol.bit (decide (v = t))) := by
  have size := Graph.size_of_encode_eq encoded
  have headerLength : (List.replicate G.size (Symbol.bit true) ++ [Symbol.separator]).length =
      (List.replicate H.size (Symbol.bit true) ++ [Symbol.separator]).length := by simp [size]
  have afterHeader := List.append_inj_right
    (show (List.replicate G.size (Symbol.bit true) ++ [Symbol.separator]) ++
        ((List.range G.size).flatMap (fun v => (List.range G.size).map (fun w => Symbol.bit (G.edge v w))) ++
          [Symbol.separator] ++ (List.range G.size).map (fun v => .bit (decide (v = s)))) =
      (List.replicate H.size (Symbol.bit true) ++ [Symbol.separator]) ++
        ((List.range H.size).flatMap (fun v => (List.range H.size).map (fun w => Symbol.bit (H.edge v w))) ++
          [Symbol.separator] ++ (List.range H.size).map (fun v => .bit (decide (v = t)))) from
        by simpa only [Graph.encode, List.append_assoc] using encoded) headerLength
  simp only [List.append_assoc] at afterHeader
  obtain ⟨matrix, afterMatrix⟩ := List.append_inj afterHeader
    (by rw [matrix_length, matrix_length, size])
  exact ⟨matrix, List.cons.inj afterMatrix |>.2⟩

theorem Graph.edges_of_encode_eq {G H : Graph} {s t : ℕ} (encoded : G.encode s = H.encode t) :
    ∀ v w, G.edge v w = H.edge v w := by
  have size := Graph.size_of_encode_eq encoded
  have matrix := (Graph.matrix_and_start_of_encode_eq encoded).1
  rw [← size] at matrix
  have rows := flatMap_blocks_injective (List.range G.size)
    (fun v => (List.range G.size).map (fun w => Symbol.bit (G.edge v w)))
    (fun v => (List.range G.size).map (fun w => Symbol.bit (H.edge v w)))
    (by simp) matrix
  intro v w
  by_cases insideV : v < G.size
  · by_cases insideW : w < G.size
    · have row := rows v (List.mem_range.mpr insideV)
      have cell := congrArg (fun word : List Symbol => word[w]?) row
      simpa [List.getElem?_map, List.getElem?_range, insideW] using cell
    · rw [G.outside v w (Or.inr (by omega)), H.outside v w (Or.inr (by omega))]
  · rw [G.outside v w (Or.inl (by omega)), H.outside v w (Or.inl (by omega))]

theorem Graph.encode_injective {G H : Graph} {s t : ℕ}
    (start : s < G.size) (encoded : G.encode s = H.encode t) : G = H ∧ s = t := by
  have size := Graph.size_of_encode_eq encoded
  have sameGraph := Graph.ext G H size (Graph.edges_of_encode_eq encoded)
  subst H
  have onehot := (Graph.matrix_and_start_of_encode_eq encoded).2
  have atStart := congrArg (fun word : List Symbol => word[s]?) onehot
  have sameStart : s = t := by
    simpa [List.getElem?_map, List.getElem?_range, start] using atStart
  exact ⟨rfl, sameStart⟩

end ComplexityOfGenerators.Examples.HAMPATH
