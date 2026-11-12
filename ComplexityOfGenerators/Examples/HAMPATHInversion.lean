import ComplexityOfGenerators.Examples.HAMPATHPaths

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

theorem Graph.ext (G H : Graph) (size : G.size = H.size)
    (edges : ∀ v w, G.edge v w = H.edge v w) : G = H := by
  have edge : G.edge = H.edge := funext fun v => funext (edges v)
  cases G
  cases H
  cases size
  cases edge
  rfl

/-- Every graph deleting to `G` is recovered by choosing exactly its incident
edges; insertion introduces no restriction on those independent choices. -/
theorem Graph.insert_delete (G : Graph) (s : ℕ) (hs : s < G.size) :
    (G.delete s).insert s (fun v => G.edge (expand s v) s)
      (fun w => G.edge s (expand s w)) = G := by
  have size : (G.delete s).size + 1 = G.size := by
    change G.size - 1 + 1 = G.size
    omega
  apply Graph.ext _ _ size
  intro v w
  change (if v < (G.delete s).size + 1 ∧ w < (G.delete s).size + 1 ∧ v ≠ w then
    if v = s then G.edge s (expand s (contract s w))
    else if w = s then G.edge (expand s (contract s v)) s
    else (G.delete s).edge (contract s v) (contract s w)
    else false) = G.edge v w
  rw [size]
  by_cases hv : v < G.size
  · by_cases hw : w < G.size
    · by_cases different : v ≠ w
      · have inside : v < G.size ∧ w < G.size ∧ v ≠ w := ⟨hv, hw, different⟩
        rw [ite_eq_left inside]
        by_cases vs : v = s
        · subst v
          have ws : w ≠ s := Ne.symm different
          simp [expand_contract ws]
        · by_cases ws : w = s
          · subst w
            simp [vs, expand_contract vs]
          · simp only [ite_eq_right vs, ite_eq_right ws]
            exact G.delete_edge_contract hs hv hw vs ws
      · have equal : v = w := by simpa using different
        subst w
        simp [G.loopFree]
    · have outside := G.outside v w (Or.inr (by omega))
      simp [hw, outside]
  · have outside := G.outside v w (Or.inl (by omega))
    simp [hv, outside]

/-- The singleton is the concrete rank-zero seed at every productive target
length `f(M)`, rather than an arbitrary assumed base language. -/
def singleton : Graph where
  size := 1
  edge := fun _ _ => false
  outside := fun _ _ _ => rfl
  loopFree := fun _ => rfl

theorem singleton_hamiltonian : HamiltonianFrom singleton 0 := by
  refine ⟨[0], by simp, by simp, ?_, trivial⟩
  intro v
  change v ∈ [0] ↔ v < 1
  simp only [List.mem_singleton]
  omega

theorem singleton_encoding : singleton.encode 0 =
    [.bit true, .separator, .bit false, .separator, .bit true] := by
  rfl

theorem singleton_rank : rank singleton.size = 0 := by
  simp [singleton, rank, width, Nat.clog_one_right]

theorem singleton_width : width singleton.size = 0 := by
  simp [singleton, width, Nat.clog_one_right]

/-- Full semantic inverse-fibre description for a chosen insertion position.
The forthcoming finite sampler has only to select these incident-edge bits. -/
theorem inverse_fibre_incident_choices (H G : Graph) (s : ℕ)
    (size : G.size = H.size + 1) (start : s < G.size) :
    G.delete s = H ↔ ∃ incoming outgoing : ℕ → Bool,
      H.insert s incoming outgoing = G := by
  constructor
  · intro deleted
    refine ⟨(fun v => G.edge (expand s v) s),
      (fun w => G.edge s (expand s w)), ?_⟩
    rw [← deleted]
    exact G.insert_delete s start
  · rintro ⟨incoming, outgoing, rfl⟩
    apply Graph.ext
    · simp [Graph.insert, Graph.delete]
    · exact H.delete_insert_edges (by simpa [Graph.insert] using start)
        incoming outgoing

end ComplexityOfGenerators.Examples.HAMPATH
