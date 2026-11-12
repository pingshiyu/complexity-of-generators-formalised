import ComplexityOfGenerators.Examples.HAMPATH

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

theorem contract_lt_pred {k s v : ℕ} (hs : s < k) (hv : v < k)
    (different : v ≠ s) : contract s v < k - 1 := by
  unfold contract
  split <;> omega

theorem Graph.delete_edge_contract (G : Graph) {s v w : ℕ}
    (hs : s < G.size) (hv : v < G.size) (hw : w < G.size)
    (vs : v ≠ s) (ws : w ≠ s) :
    (G.delete s).edge (contract s v) (contract s w) = G.edge v w := by
  simp only [Graph.delete, contract_lt_pred hs hv vs, contract_lt_pred hs hw ws,
    and_self, ite_true, expand_contract vs, expand_contract ws]

theorem follows_map_on {e e' : ℕ → ℕ → Bool} (f : ℕ → ℕ) (path : List ℕ)
    (respects : ∀ v ∈ path, ∀ w ∈ path, e' (f v) (f w) = e v w) :
    Follows e' (path.map f) ↔ Follows e path := by
  induction path with
  | nil => trivial
  | cons v rest ih =>
    cases rest with
    | nil => trivial
    | cons w rest =>
      have edge := respects v (by simp) w (by simp)
      have tail := ih (by
        intro a ha b hb
        exact respects a (by simp [ha]) b (by simp [hb]))
      simp only [List.map_cons, Follows, edge]
      exact and_congr Iff.rfl (by simpa only [List.map_cons] using tail)

theorem delete_hamiltonian_tail (G : Graph) {s u : ℕ} {rest : List ℕ}
    (nodup : (s :: u :: rest).Nodup)
    (covers : ∀ v, v ∈ s :: u :: rest ↔ v < G.size)
    (follows : Follows G.edge (s :: u :: rest)) :
    HamiltonianFrom (G.delete s) (contract s u) := by
  have hs : s < G.size := (covers s).mp (by simp)
  have tailGood : ∀ v ∈ u :: rest, v < G.size ∧ v ≠ s := by
    intro v member
    refine ⟨(covers v).mp (by simp [member]), ?_⟩
    intro equal
    have absent := (List.nodup_cons.mp nodup).1
    exact absent (equal ▸ member)
  refine ⟨(u :: rest).map (contract s), by simp, ?_, ?_, ?_⟩
  · apply List.Nodup.map_on _ (List.nodup_cons.mp nodup).2
    intro v hv w hw equal
    have vback := expand_contract (tailGood v hv).2
    have wback := expand_contract (tailGood w hw).2
    exact vback.symm.trans ((congrArg (expand s) equal).trans wback)
  · intro v
    constructor
    · intro member
      obtain ⟨w, sourceMember, rfl⟩ := List.mem_map.mp member
      exact contract_lt_pred hs (tailGood w sourceMember).1 (tailGood w sourceMember).2
    · intro bound
      have lifted : expand s v < G.size := by
        have := expand_lt (s := s) bound
        change expand s v < (G.delete s).size + 1 at this
        change v < G.size - 1 at bound
        change expand s v < G.size
        change expand s v < (G.size - 1) + 1 at this
        omega
      have present : expand s v ∈ u :: rest := by
        have member := (covers (expand s v)).mpr lifted
        rcases List.mem_cons.mp member with equal | member
        · exact False.elim (expand_ne s v equal)
        · exact member
      exact List.mem_map.mpr ⟨expand s v, present, contract_expand s v⟩
  · apply (follows_map_on (contract s) (u :: rest) ?_).mpr follows.2
    intro v hv w hw
    exact G.delete_edge_contract hs (tailGood v hv).1 (tailGood w hw).1
      (tailGood v hv).2 (tailGood w hw).2

theorem hamiltonian_of_deleted (G : Graph) {s u : ℕ}
    (hs : s < G.size) (hu : u < G.size) (different : u ≠ s)
    (next : G.edge s u = true)
    (path : HamiltonianFrom (G.delete s) (contract s u)) :
    HamiltonianFrom G s := by
  obtain ⟨vertices, head, nodup, covers, follows⟩ := path
  have positive : 0 < G.size := by omega
  refine ⟨s :: vertices.map (expand s), by simp, ?_, ?_, ?_⟩
  · simp only [List.nodup_cons]
    constructor
    · intro h
      obtain ⟨v, _, same⟩ := List.mem_map.mp h
      exact expand_ne s v same
    · exact nodup.map (expand_injective s)
  · intro v
    constructor
    · intro member
      rcases List.mem_cons.mp member with equal | member
      · subst v; exact hs
      · obtain ⟨w, sourceMember, rfl⟩ := List.mem_map.mp member
        have bound := (covers w).mp sourceMember
        change w < G.size - 1 at bound
        have := expand_lt (s := s) bound
        omega
    · intro bound
      by_cases equal : v = s
      · exact List.mem_cons.mpr (Or.inl equal)
      · apply List.mem_cons.mpr
        right
        exact List.mem_map.mpr ⟨contract s v,
          (covers _).mpr (contract_lt_pred hs bound equal), expand_contract equal⟩
  · have transferred : Follows G.edge (vertices.map (expand s)) := by
      apply (follows_map_on (expand s) vertices ?_).mpr follows
      intro v hv w hw
      have vb := (covers v).mp hv
      have wb := (covers w).mp hw
      change v < G.size - 1 at vb
      change w < G.size - 1 at wb
      simp [Graph.delete, vb, wb]
    cases vertices with
    | nil => simp at head
    | cons v rest =>
      have equal : v = contract s u := by simpa using head
      subst v
      change G.edge s (expand s (contract s u)) = true ∧ _
      exact ⟨by simpa [expand_contract different] using next, transferred⟩

/-- The semantic deletion recurrence of the paper's Hamiltonian-path verifier. -/
theorem hamiltonian_delete_iff (G : Graph) (s : ℕ) (size : 2 ≤ G.size) :
    HamiltonianFrom G s ↔
      s < G.size ∧ ∃ u, u < G.size ∧ u ≠ s ∧ G.edge s u = true ∧
        HamiltonianFrom (G.delete s) (contract s u) := by
  constructor
  · rintro ⟨vertices, head, nodup, covers, follows⟩
    cases vertices with
    | nil => simp at head
    | cons v rest =>
      have equal : v = s := by simpa using head
      subst v
      have hs : s < G.size := (covers s).mp (by simp)
      refine ⟨hs, ?_⟩
      cases rest with
      | nil =>
        have other : ∃ u, u < G.size ∧ u ≠ s := by
          by_cases zero : s = 0
          · exact ⟨1, by omega, by omega⟩
          · exact ⟨0, by omega, by omega⟩
        obtain ⟨u, bound, different⟩ := other
        have member := (covers u).mpr bound
        simp at member
        exact False.elim (different member)
      | cons u tail =>
        have hu := (covers u).mp (by simp)
        have different : u ≠ s := by
          intro eq
          have absent := (List.nodup_cons.mp nodup).1
          exact absent (by simp [eq])
        exact ⟨u, hu, different, follows.1,
          delete_hamiltonian_tail G nodup covers follows⟩
  · rintro ⟨hs, u, hu, different, next, remaining⟩
    exact hamiltonian_of_deleted G hs hu different next remaining

end ComplexityOfGenerators.Examples.HAMPATH
