import ComplexityOfGenerators.Examples.HAMPATHInversion

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

theorem rank_positive_iff (k : ℕ) : 0 < rank k ↔ 0 < width k := by
  cases k with
  | zero => simp [width]
  | succ n =>
    cases n with
    | zero => simp [rank_succ, width, Nat.clog_one_right]
    | succ n =>
      have positive : 0 < width (n + 1 + 1) := Nat.clog_pos (by decide) (by omega)
      rw [rank_succ]
      omega

theorem rank_encoding_bound (k : ℕ) : rank k ≤ encodingLength k := by
  have := rank_le_square k
  unfold encodingLength
  omega

theorem width_encoding_log_bound (k : ℕ) :
    width k ≤ Nat.log 2 (encodingLength k) + 1 := by
  have bound : k ≤ encodingLength k := by unfold encodingLength; omega
  exact (width_log_bound k).trans (Nat.add_le_add_right (Nat.log_mono_right bound) 1)

theorem HamiltonianFrom.start_bound {G : Graph} {start : ℕ}
    (path : HamiltonianFrom G start) : start < G.size := by
  obtain ⟨vertices, head, _, covers, _⟩ := path
  cases vertices with
  | nil => simp at head
  | cons v rest =>
    have equal : v = start := by simpa using head
    subst v
    exact (covers start).mp (by simp)

theorem rank_zero_iff_singleton_size {G : Graph} {start : ℕ}
    (path : HamiltonianFrom G start) : rank G.size = 0 ↔ G.size = 1 := by
  have positive := path.start_bound
  constructor
  · intro zero
    have widthZero : ¬ 0 < width G.size := by rw [← rank_positive_iff, zero]; omega
    by_contra notOne
    have two : 1 < G.size := by omega
    exact widthZero (Nat.clog_pos (by decide) two)
  · intro size
    simp [size, rank_succ, width, Nat.clog_one_right]

theorem rank_zero_graph (G : Graph) {start : ℕ} (path : HamiltonianFrom G start)
    (zero : rank G.size = 0) : G = singleton ∧ start = 0 := by
  have size : G.size = 1 := (rank_zero_iff_singleton_size path).mp zero
  have startBound := path.start_bound
  refine ⟨?_, by omega⟩
  apply Graph.ext _ _ size
  intro v w
  change G.edge v w = false
  by_cases equal : v = w
  · subst w; exact G.loopFree v
  · apply G.outside
    rw [size]
    omega

theorem rank_zero_encoding (G : Graph) {start : ℕ} (path : HamiltonianFrom G start)
    (zero : rank G.size = 0) :
    G.encode start = [.bit true, .separator, .bit false, .separator, .bit true] := by
  obtain ⟨rfl, rfl⟩ := rank_zero_graph G path zero
  exact singleton_encoding

end ComplexityOfGenerators.Examples.HAMPATH
