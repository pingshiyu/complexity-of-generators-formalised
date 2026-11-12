import ComplexityOfGenerators.Examples.HAMPATHLabels

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

/-- Concatenated next-vertex blocks, with the current graph relabelled after
each deletion. The empty certificate belongs exactly to the singleton base. -/
def graphCertificates (G : Graph) (start : ℕ) : Set (List Symbol) :=
  if _small : G.size ≤ 1 then
    {certificate | certificate = [] ∧ G.size = 1 ∧ start = 0}
  else
    {certificate | start < G.size ∧ ∃ next tail,
      next < G.size ∧ next ≠ start ∧ G.edge start next = true ∧
      tail ∈ graphCertificates (G.delete start) (contract start next) ∧
      certificate = vertexLabel G.size next ++ tail}
termination_by G.size
decreasing_by simp only [Graph.delete]; omega

theorem Graph.eq_singleton_of_size (G : Graph) (size : G.size = 1) : G = singleton := by
  apply Graph.ext _ _ size
  intro v w
  change G.edge v w = false
  by_cases equal : v = w
  · subst w; exact G.loopFree v
  · apply G.outside
    rw [size]
    omega

theorem singleton_size_hamiltonian (G : Graph) (start : ℕ) (size : G.size ≤ 1) :
    HamiltonianFrom G start ↔ G.size = 1 ∧ start = 0 := by
  constructor
  · intro member
    have bound := member.start_bound
    omega
  · rintro ⟨size, rfl⟩
    rw [G.eq_singleton_of_size size]
    exact singleton_hamiltonian

/-- These concrete block certificates recognize exactly Hamiltonian paths,
rather than assuming a verifier for an abstract certificate relation. -/
theorem graph_certifies (G : Graph) (start : ℕ) :
    HamiltonianFrom G start ↔ (graphCertificates G start).Nonempty := by
  generalize size : G.size = n
  induction n using Nat.strong_induction_on generalizing G start with
  | h n ih =>
    rw [graphCertificates]
    split_ifs with small
    · rw [singleton_size_hamiltonian G start small]
      constructor
      · rintro ⟨size, head⟩
        exact ⟨[], rfl, size, head⟩
      · rintro ⟨_, _, size, head⟩
        exact ⟨size, head⟩
    · rw [hamiltonian_delete_iff G start (by omega)]
      have smaller : (G.delete start).size < n := by simp only [Graph.delete]; omega
      constructor
      · rintro ⟨startBound, next, nextBound, different, edge, member⟩
        obtain ⟨tail, certified⟩ :=
          (ih _ smaller (G.delete start) (contract start next) rfl).mp member
        exact ⟨vertexLabel G.size next ++ tail, startBound,
          next, tail, nextBound, different, edge, certified, rfl⟩
      · rintro ⟨certificate, startBound, next, tail, nextBound, different, edge, certified, _⟩
        exact ⟨startBound, next, nextBound, different, edge,
          (ih _ smaller (G.delete start) (contract start next) rfl).mpr ⟨tail, certified⟩⟩

theorem graph_certificate_length (G : Graph) (start : ℕ) (certificate : List Symbol)
    (member : certificate ∈ graphCertificates G start) : certificate.length = rank G.size := by
  generalize size : G.size = n
  induction n using Nat.strong_induction_on generalizing G start certificate with
  | h n ih =>
    rw [graphCertificates] at member
    split_ifs at member with small
    · obtain ⟨rfl, singletonSize, _⟩ := member
      have nOne : n = 1 := by omega
      simp [nOne, rank_succ, width, Nat.clog_one_right]
    · obtain ⟨_, next, tail, _, _, _, tailMember, rfl⟩ := member
      have smaller : (G.delete start).size < n := by simp only [Graph.delete]; omega
      have length := ih _ smaller (G.delete start) (contract start next) tail tailMember rfl
      rw [List.length_append, vertexLabel_length, length]
      have positive : 0 < G.size := by omega
      have recurrence := rank_succ (G.size - 1)
      rw [Nat.sub_add_cancel positive] at recurrence
      simpa [Graph.delete, Nat.add_comm, size] using recurrence.symm

theorem graph_certificate_split (G : Graph) (start : ℕ) (large : 2 ≤ G.size)
    (certificate : List Symbol) :
    certificate ∈ graphCertificates G start ↔
      start < G.size ∧ ∃ next tail, next < G.size ∧ next ≠ start ∧
        G.edge start next = true ∧
        tail ∈ graphCertificates (G.delete start) (contract start next) ∧
        certificate = vertexLabel G.size next ++ tail := by
  rw [graphCertificates, dite_eq_right (by omega)]
  rfl

end ComplexityOfGenerators.Examples.HAMPATH
