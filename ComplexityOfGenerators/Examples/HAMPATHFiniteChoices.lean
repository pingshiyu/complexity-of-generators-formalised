import ComplexityOfGenerators.Examples.HAMPATHInverseWords

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

def rowFromBits (bits : List Bool) (vertex : ℕ) : Bool := bits[vertex]?.getD false

def rowBits (size : ℕ) (row : ℕ → Bool) : List Bool := (List.range size).map row

@[simp] theorem rowBits_length (size : ℕ) (row : ℕ → Bool) : (rowBits size row).length = size := by
  simp [rowBits]

theorem rowBits_lookup (size : ℕ) (row : ℕ → Bool) (vertex : ℕ) (bound : vertex < size) :
    rowFromBits (rowBits size row) vertex = row vertex := by
  simp [rowFromBits, rowBits, List.getElem?_map, List.getElem?_range bound]

theorem Graph.insert_rows_congr (G : Graph) (position : ℕ) (positionBound : position ≤ G.size)
    (incoming outgoing incoming' outgoing' : ℕ → Bool)
    (incomingEq : ∀ v < G.size, incoming v = incoming' v)
    (outgoingEq : ∀ v < G.size, outgoing v = outgoing' v) :
    G.insert position incoming outgoing = G.insert position incoming' outgoing' := by
  apply Graph.ext (G.insert position incoming outgoing) (G.insert position incoming' outgoing') rfl
  intro v w
  change (if v < G.size + 1 ∧ w < G.size + 1 ∧ v ≠ w then
    if v = position then outgoing (contract position w)
    else if w = position then incoming (contract position v)
    else G.edge (contract position v) (contract position w) else false) =
    (if v < G.size + 1 ∧ w < G.size + 1 ∧ v ≠ w then
    if v = position then outgoing' (contract position w)
    else if w = position then incoming' (contract position v)
    else G.edge (contract position v) (contract position w) else false)
  by_cases inside : v < G.size + 1 ∧ w < G.size + 1 ∧ v ≠ w
  · rw [ite_eq_left inside, ite_eq_left inside]
    by_cases vs : v = position
    · have different : w ≠ position := by intro equal; exact inside.2.2 (vs.trans equal.symm)
      have bound := contract_lt (Nat.lt_succ_of_le positionBound) inside.2.1 different
      rw [ite_eq_left vs, ite_eq_left vs]
      exact outgoingEq _ bound
    · by_cases ws : w = position
      · have bound := contract_lt (Nat.lt_succ_of_le positionBound) inside.1 vs
        rw [ite_eq_right vs, ite_eq_right vs, ite_eq_left ws, ite_eq_left ws]
        exact incomingEq _ bound
      · rw [ite_eq_right vs, ite_eq_right vs, ite_eq_right ws, ite_eq_right ws]
  · rw [ite_eq_right inside, ite_eq_right inside]

/-- Only the 2|V| incident-edge coins are observed. Arbitrary functions in the
semantic inverse description can therefore be replaced by finite bit rows. -/
theorem Graph.insert_finite_rows (G : Graph) (position : ℕ) (bound : position ≤ G.size)
    (incoming outgoing : ℕ → Bool) :
    G.insert position (rowFromBits (rowBits G.size incoming))
      (rowFromBits (rowBits G.size outgoing)) = G.insert position incoming outgoing := by
  apply G.insert_rows_congr position bound
  · intro v hv; exact rowBits_lookup G.size incoming v hv
  · intro v hv; exact rowBits_lookup G.size outgoing v hv

theorem inverseFibre_finite_choices (H : Graph) (start : ℕ)
    (member : HamiltonianFrom H start) (M : ℕ) (label : List Symbol) (nonempty : label ≠ []) :
    selfReduction.inverseFibre (encodingLength M) (H.encode start) label =
      {word | H.size + 1 ≤ M ∧ ∃ position incoming outgoing,
        position ≤ H.size ∧ incoming.length = H.size ∧ outgoing.length = H.size ∧
        rowFromBits outgoing start = true ∧
        label = vertexLabel (H.size + 1) (expand position start) ∧
        word = (H.insert position (rowFromBits incoming) (rowFromBits outgoing)).encode position} := by
  rw [inverseFibre_nonempty_label H start member M label nonempty]
  ext word
  constructor
  · rintro ⟨sizeBound, position, incoming, outgoing, positionBound, required, labelEq, equal⟩
    refine ⟨sizeBound, position, rowBits H.size incoming, rowBits H.size outgoing,
      positionBound, rowBits_length _ _, rowBits_length _ _, ?_, labelEq, ?_⟩
    · rw [rowBits_lookup H.size outgoing start member.start_bound]
      exact required
    · rw [Graph.insert_finite_rows H position positionBound incoming outgoing]
      exact equal
  · rintro ⟨sizeBound, position, incoming, outgoing, positionBound, _, _, required, labelEq, equal⟩
    exact ⟨sizeBound, position, rowFromBits incoming, rowFromBits outgoing,
      positionBound, required, labelEq, equal⟩

end ComplexityOfGenerators.Examples.HAMPATH
