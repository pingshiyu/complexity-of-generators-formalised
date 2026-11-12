import ComplexityOfGenerators.Examples.HAMPATHAncestors

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

theorem Graph.encode_ne_nil (G : Graph) (start : ℕ) : G.encode start ≠ [] := by
  intro empty
  have length := congrArg List.length empty
  rw [G.encode_length] at length
  simp only [List.length_nil, encodingLength] at length
  omega

theorem width_positive_size {size : ℕ} (positive : 0 < width size) : 2 ≤ size := by
  by_contra contrary
  have small : size = 0 ∨ size = 1 := by omega
  rcases small with rfl | rfl <;> simp [width, Nat.clog_one_right] at positive

theorem Graph.insert_delete_eq (G : Graph) (position : ℕ) (bound : position ≤ G.size)
    (incoming outgoing : ℕ → Bool) : (G.insert position incoming outgoing).delete position = G := by
  apply Graph.ext
  · simp [Graph.insert, Graph.delete]
  · exact G.delete_insert_edges bound incoming outgoing

/-- The insertion construction reaches the exact word-level inverse fibre.
It chooses the new start position and every incident edge, forces the edge to
the old start, and rejects exactly the capacity or label mismatches. -/
theorem inverseFibre_nonempty_label (H : Graph) (start : ℕ)
    (member : HamiltonianFrom H start) (M : ℕ) (label : List Symbol) (nonempty : label ≠ []) :
    selfReduction.inverseFibre (encodingLength M) (H.encode start) label =
      {word | H.size + 1 ≤ M ∧ ∃ position incoming outgoing,
        position ≤ H.size ∧ outgoing start = true ∧
        label = vertexLabel (H.size + 1) (expand position start) ∧
        word = (H.insert position incoming outgoing).encode position} := by
  ext word
  constructor
  · rintro ⟨ancestor, reduction, labelLength⟩
    rw [ancestors_eq] at ancestor
    obtain ⟨G, source, sourceMember, sizeBound, equal⟩ := ancestor
    change wordReduce word label = H.encode start at reduction
    change label.length = wordWidth word at labelLength
    rw [← equal, wordWidth_encode G source sourceMember.start_bound] at labelLength
    have widthPositive : 0 < width G.size := by
      rw [← labelLength]
      exact List.length_pos_iff.mpr nonempty
    have large := width_positive_size widthPositive
    rw [← equal] at reduction
    cases decoded : decodeLabel G.size label with
    | none =>
      have impossible : [] = H.encode start := by
        simpa [wordReduce, decode_encode G source sourceMember.start_bound,
          show ¬ G.size ≤ 1 by omega, decoded] using reduction
      exact False.elim (H.encode_ne_nil start impossible.symm)
    | some next =>
      by_cases good : next ≠ source ∧ G.edge source next = true
      · obtain ⟨nextBound, labelEq⟩ := decodeLabel_sound G.size label next decoded
        have reduced : wordReduce (G.encode source) label =
            (G.delete source).encode (contract source next) := by
          rw [labelEq]
          exact wordReduce_encode_label G source next sourceMember.start_bound large nextBound good.1 good.2
        rw [reduced] at reduction
        obtain ⟨deleted, nextStart⟩ := Graph.encode_injective
          (contract_lt_pred sourceMember.start_bound nextBound good.1) reduction
        have size : G.size = H.size + 1 := by
          have same := congrArg Graph.size deleted
          simp only [Graph.delete] at same
          omega
        have sourceBound : source ≤ H.size := by have := sourceMember.start_bound; omega
        let incoming := fun v => G.edge (expand source v) source
        let outgoing := fun v => G.edge source (expand source v)
        have recovered : H.insert source incoming outgoing = G := by
          rw [← deleted]
          exact G.insert_delete source sourceMember.start_bound
        have nextEq : expand source start = next := by
          rw [← nextStart]
          exact expand_contract good.1
        refine ⟨by omega, source, incoming, outgoing, sourceBound, ?_, ?_, ?_⟩
        · change G.edge source (expand source start) = true
          rw [nextEq]
          exact good.2
        · simpa [size, nextEq] using labelEq
        · rw [recovered]
          exact equal.symm
      · have impossible : [] = H.encode start := by
          simpa [wordReduce, decode_encode G source sourceMember.start_bound,
            show ¬ G.size ≤ 1 by omega, decoded, good] using reduction
        exact False.elim (H.encode_ne_nil start impossible.symm)
  · rintro ⟨sizeBound, position, incoming, outgoing, positionBound, required, labelEq, rfl⟩
    let G := H.insert position incoming outgoing
    have sourceMember : HamiltonianFrom G position :=
      prepend_preserves_hamiltonian H positionBound incoming outgoing required member
    have sourceBound := sourceMember.start_bound
    have nextBound : expand position start < G.size := expand_lt member.start_bound
    have different : expand position start ≠ position := expand_ne _ _
    have large : 2 ≤ G.size := by
      have := member.start_bound
      change 2 ≤ H.size + 1
      omega
    have edge : G.edge position (expand position start) = true := by
      have nextNumeric : expand position start ≤ H.size := by
        change expand position start < H.size + 1 at nextBound
        omega
      simp [G, Graph.insert, positionBound, nextNumeric, Ne.symm different,
        contract_expand, required]
    refine ⟨?_, ?_, ?_⟩
    · rw [ancestors_eq]
      exact ⟨G, position, sourceMember, sizeBound, rfl⟩
    · change wordReduce (G.encode position) label = H.encode start
      rw [labelEq]
      change wordReduce (G.encode position) (vertexLabel G.size (expand position start)) = H.encode start
      rw [wordReduce_encode_label G position _ sourceBound large nextBound different edge,
        Graph.insert_delete_eq H position positionBound incoming outgoing, contract_expand]
    · change label.length = wordWidth (G.encode position)
      rw [labelEq, vertexLabel_length, wordWidth_encode G position sourceBound]
      rfl

theorem inverseFibre_empty (H : Graph) (start : ℕ) (member : HamiltonianFrom H start)
    (M : ℕ) :
    selfReduction.inverseFibre (encodingLength M) (H.encode start) [] =
      {word | H.size = 1 ∧ H.size ≤ M ∧ word = H.encode start} := by
  ext word
  constructor
  · rintro ⟨ancestor, reduction, labelLength⟩
    rw [ancestors_eq] at ancestor
    obtain ⟨G, source, sourceMember, sizeBound, equal⟩ := ancestor
    change wordReduce word [] = H.encode start at reduction
    change 0 = wordWidth word at labelLength
    rw [← equal, wordWidth_encode G source sourceMember.start_bound] at labelLength
    have zeroRank : rank G.size = 0 := by
      have notPositive : ¬ 0 < rank G.size := by
        intro positive
        have := (rank_positive_iff G.size).mp positive
        omega
      omega
    have singletonSize : G.size = 1 := (rank_zero_iff_singleton_size sourceMember).mp zeroRank
    have identity : wordReduce word [] = word := by
      rw [← equal]
      simp [wordReduce, decode_encode G source sourceMember.start_bound, singletonSize]
    rw [identity] at reduction
    have sameSize := Graph.size_of_encode_eq (equal.trans reduction)
    refine ⟨by omega, ?_, reduction⟩
    omega
  · rintro ⟨singletonSize, sizeBound, rfl⟩
    refine ⟨?_, ?_, ?_⟩
    · rw [ancestors_eq]
      exact ⟨H, start, member, sizeBound, rfl⟩
    · change wordReduce _ [] = _
      simp [wordReduce, decode_encode H start member.start_bound, singletonSize]
    · change 0 = wordWidth _
      simp [wordWidth_encode H start member.start_bound, singletonSize,
        width, Nat.clog_one_right]

end ComplexityOfGenerators.Examples.HAMPATH
