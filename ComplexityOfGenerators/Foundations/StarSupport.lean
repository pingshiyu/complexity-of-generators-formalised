import ComplexityOfGenerators.Foundations.IndexedSupportClosure

/-! Positive-factor presentations of Kleene star, used by the native random
DP construction. Empty factors can always be omitted. -/

namespace ComplexityOfGenerators.IndexedSupport

variable {α : Type} (L : Language α)

theorem nil_mem_star : [] ∈ star L := ⟨[], by simp, rfl⟩

theorem cons_mem_star {u v : List α} (left : u ∈ L) (positive : u ≠ []) (right : v ∈ star L) :
    u ++ v ∈ star L := by
  obtain ⟨words, members, rfl⟩ := right
  refine ⟨u :: words, ?_, rfl⟩
  intro w hw
  rcases List.mem_cons.mp hw with rfl | hw
  · exact ⟨left, positive⟩
  · exact members w hw

theorem star_decompose {word : List α} (member : word ∈ star L) (positive : word ≠ []) :
    ∃ u ∈ L, u ≠ [] ∧ ∃ v ∈ star L, u ++ v = word := by
  obtain ⟨words, members, rfl⟩ := member
  cases words with
  | nil => exact False.elim (positive rfl)
  | cons u rest =>
    refine ⟨u, (members u (by simp)).1, (members u (by simp)).2, rest.flatten, ?_, rfl⟩
    refine ⟨rest, ?_, rfl⟩
    intro v hv
    exact members v (by simp [hv])

theorem star_zero_slice : lengthSlice (star L) 0 = {[]} := by
  ext word
  constructor
  · intro member
    exact List.length_eq_zero_iff.mp member.2
  · intro member
    change word = [] at member
    subst word
    exact ⟨nil_mem_star L, rfl⟩

/-- Every positive target has a first positive source length and a strictly
smaller star suffix. This is the acyclic DP recurrence. -/
theorem star_slice_decompose {n : ℕ} (positive : 0 < n) {word : List α}
    (member : word ∈ lengthSlice (star L) n) :
    ∃ j, 1 ≤ j ∧ j ≤ n ∧ ∃ u ∈ lengthSlice L j,
      ∃ v ∈ lengthSlice (star L) (n - j), u ++ v = word := by
  have nonempty : word ≠ [] := by intro equal; have := member.2; simp [equal] at this; omega
  obtain ⟨u, left, positiveU, v, right, rfl⟩ := star_decompose L member.1 nonempty
  have lengths : u.length + v.length = n := by simpa using member.2
  refine ⟨u.length, List.length_pos_iff.mpr positiveU, by omega, u, ⟨left, rfl⟩,
    v, ⟨right, by omega⟩, rfl⟩

theorem star_slice_compose {n j : ℕ} {u v : List α} (positive : 0 < j) (index : j ≤ n)
    (left : u ∈ lengthSlice L j) (right : v ∈ lengthSlice (star L) (n - j)) :
    u ++ v ∈ lengthSlice (star L) n := by
  refine ⟨cons_mem_star L left.1 ?_ right.1, ?_⟩
  · intro empty
    have := left.2
    simp [empty] at this
    omega
  · simp only [List.length_append, left.2, right.2]
    omega

end ComplexityOfGenerators.IndexedSupport
