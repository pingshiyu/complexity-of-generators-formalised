import ComplexityOfGenerators.SelfReducibility

/-! Certificate decomposition, iterated reductions, and ancestor sets from
Appendix A.23. These arguments use Mathlib's reflexive transitive closure. -/

namespace ComplexityOfGenerators.SelfReduction

variable {α : Type} {L : Language α} (R : SelfReduction L)

/-- Lemma A.23.1, including the zero-width case. -/
theorem mem_of_reduce_mem {x w : Word α} (length : w.length = R.width x)
    (member : R.reduce x w ∈ L) : x ∈ L := by
  obtain ⟨c, certified⟩ := (R.certifies _).mp member
  exact (R.certifies x).mpr ⟨w ++ c, (R.split x _).mpr ⟨w, c, length, certified, rfl⟩⟩

theorem step_rank_lt {x y : Word α} (step : R.Step x y) : R.rank y < R.rank x := by
  obtain ⟨w, positive, _, rfl⟩ := step
  have bound := R.rank_reduce x w
  have := (R.positive x).mpr positive
  omega

theorem step_length_le {x y : Word α} (step : R.Step x y) : y.length ≤ x.length := by
  obtain ⟨w, _, _, rfl⟩ := step
  exact R.length_reduce x w

theorem step_mem {x y : Word α} (step : R.Step x y) (member : y ∈ L) : x ∈ L := by
  obtain ⟨w, _, length, rfl⟩ := step
  exact R.mem_of_reduce_mem length member

theorem path_length_le {x y : Word α} (path : R.Path x y) : y.length ≤ x.length := by
  induction path with
  | refl => exact le_rfl
  | tail _ step ih => exact (R.step_length_le step).trans ih

theorem path_rank_le {x y : Word α} (path : R.Path x y) : R.rank y ≤ R.rank x := by
  induction path with
  | refl => exact le_rfl
  | tail _ step ih => exact (R.step_rank_lt step).le.trans ih

theorem path_mem {x y : Word α} (path : R.Path x y) (member : y ∈ L) : x ∈ L := by
  induction path with
  | refl => exact member
  | tail _ step ih => exact ih (R.step_mem step member)

/-- Every member of positive certificate length has a genuine reduction to
another member. The hypothesis `x ∈ L`, omitted from the printed statement of
Lemma A.23.2 but used in its proof, is essential. -/
theorem exists_step {x : Word α} (member : x ∈ L) (positive : 0 < R.rank x) :
    ∃ y ∈ L, R.Step x y := by
  obtain ⟨c, certified⟩ := (R.certifies x).mp member
  obtain ⟨w, d, length, tail, _⟩ := (R.split x c).mp certified
  exact ⟨R.reduce x w, (R.certifies _).mpr ⟨d, tail⟩,
    w, (R.positive x).mp positive, length, rfl⟩

/-- Lemma A.23.2: a member reduces to a zero-certificate member. This also
covers the already-zero case by the reflexive path. -/
theorem exists_base_path {x : Word α} (member : x ∈ L) :
    ∃ y ∈ L, R.rank y = 0 ∧ R.Path x y := by
  generalize h : R.rank x = k
  induction k using Nat.strong_induction_on generalizing x with
  | h k ih =>
    by_cases zero : R.rank x = 0
    · exact ⟨x, member, zero, .refl⟩
    · obtain ⟨z, zm, step⟩ := R.exists_step member (by omega)
      obtain ⟨y, ym, yr, path⟩ := ih (R.rank z) (by have := R.step_rank_lt step; omega) zm rfl
      exact ⟨y, ym, yr, path.head step⟩

theorem iterated_length_le {x w y : Word α} (path : R.Iterated x w y) :
    y.length ≤ x.length := by
  induction path with
  | single x w _ => exact R.length_reduce x w
  | more x w _ _ _ _ _ ih => exact ih.trans (R.length_reduce x w)

theorem iterated_rank_le {x w y : Word α} (path : R.Iterated x w y) :
    R.rank y ≤ R.rank x := by
  induction path with
  | single x w _ => exact (R.rank_reduce x w).trans (Nat.sub_le _ _)
  | more x w _ _ _ _ _ ih => exact ih.trans ((R.rank_reduce x w).trans (Nat.sub_le _ _))

/-- A *defined* iterated reduction on a nonempty string strictly decreases
rank. In particular, a zero-width recursive call cannot finish on such input. -/
theorem iterated_rank_lt {x w y : Word α} (path : R.Iterated x w y) (nonempty : w ≠ []) :
    R.rank y < R.rank x := by
  induction path with
  | single x w length =>
    apply R.step_rank_lt
    exact ⟨w, by have := List.length_pos_iff.mpr nonempty; omega, length, rfl⟩
  | more x w rest y _ remaining _ ih =>
    exact (ih remaining).trans_le ((R.rank_reduce x w).trans (Nat.sub_le _ _))

theorem iterated_path {x w y : Word α} (path : R.Iterated x w y) (nonempty : w ≠ []) :
    R.Path x y := by
  induction path with
  | single x w length =>
    exact .single ⟨w, by have := List.length_pos_iff.mpr nonempty; omega, length, rfl⟩
  | more x w rest y length remaining tail ih =>
    apply (ih remaining).head
    have decrease := R.iterated_rank_lt tail remaining
    have bound := R.rank_reduce x w
    have positive : 0 < R.rank x := by omega
    exact ⟨w, (R.positive x).mp positive, length, rfl⟩

theorem iterated_append {x w y v z : Word α} (first : R.Iterated x w y)
    (second : R.Iterated y v z) (nonempty : v ≠ []) : R.Iterated x (w ++ v) z := by
  induction first with
  | single x w length => exact .more x w v z length nonempty second
  | more x w rest y length remaining tail ih =>
    rw [List.append_assoc]
    exact .more x w (rest ++ v) z length (by simp [nonempty]) (ih second)

theorem path_eq_or_iterated {x y : Word α} (path : R.Path x y) :
    y = x ∨ ∃ w, w ≠ [] ∧ R.Iterated x w y := by
  induction path with
  | refl => exact Or.inl rfl
  | @tail y z path step ih =>
    obtain ⟨v, positive, length, rfl⟩ := step
    have nonempty : v ≠ [] := by intro h; simp [h] at length; omega
    rcases ih with rfl | ⟨w, wn, tail⟩
    · exact Or.inr ⟨v, nonempty, .single _ _ length⟩
    · exact Or.inr ⟨w ++ v, by simp [nonempty],
        R.iterated_append tail (.single _ _ length) nonempty⟩

/-- The path formulation exactly matches Definition A.23.4; it does not add
ancestors reached only by empty labels. -/
theorem mem_ancestors_iff {n : ℕ} {y : Word α} :
    y ∈ R.ancestors n ↔ y ∈ L ∧ ∃ x ∈ lengthSlice L n, R.Path x y := by
  constructor
  · rintro ⟨member, length | ⟨x, xm, w, wn, path⟩⟩
    · exact ⟨member, y, ⟨member, length⟩, .refl⟩
    · exact ⟨member, x, xm, R.iterated_path path wn⟩
  · rintro ⟨member, x, xm, path⟩
    refine ⟨member, ?_⟩
    rcases R.path_eq_or_iterated path with rfl | ⟨w, wn, path⟩
    · exact Or.inl xm.2
    · exact Or.inr ⟨x, xm, w, wn, path⟩

/-- Lemma A.23.3. -/
theorem ancestor_length_le {n : ℕ} {y : Word α} (member : y ∈ R.ancestors n) :
    y.length ≤ n := by
  obtain ⟨_, x, xm, path⟩ := R.mem_ancestors_iff.mp member
  exact (R.path_length_le path).trans xm.2.le

theorem ancestor_rank_le {n : ℕ} {y : Word α} (member : y ∈ R.ancestors n) :
    R.rank y ≤ R.rankBound n := by
  apply (R.rank_le y).trans
  exact Nat.mul_le_mul_left _ (pow_le_pow_left' (Nat.add_le_add_right (R.ancestor_length_le member) 1) _)

theorem slice_subset_ancestors (n : ℕ) : lengthSlice L n ⊆ R.ancestors n :=
  fun _ member => ⟨member.1, Or.inl member.2⟩

theorem ancestor_of_path {n : ℕ} {x y : Word α} (ancestor : x ∈ R.ancestors n)
    (path : R.Path x y) (member : y ∈ L) : y ∈ R.ancestors n := by
  obtain ⟨_, z, zm, initialPath⟩ := R.mem_ancestors_iff.mp ancestor
  exact R.mem_ancestors_iff.mpr ⟨member, z, zm, initialPath.trans path⟩

/-- Every word in the target slice can be reconstructed from a sampled base. -/
theorem slice_has_base {n : ℕ} {x : Word α} (member : x ∈ lengthSlice L n) :
    ∃ y ∈ R.bases n, R.Path x y := by
  obtain ⟨y, ym, zero, path⟩ := R.exists_base_path member.1
  exact ⟨y, ⟨R.ancestor_of_path (R.slice_subset_ancestors n member) path ym, zero⟩, path⟩

theorem bases_nonempty_iff (n : ℕ) : (R.bases n).Nonempty ↔ (lengthSlice L n).Nonempty := by
  constructor
  · rintro ⟨y, ancestor, _⟩
    obtain ⟨_, x, xm, _⟩ := R.mem_ancestors_iff.mp ancestor
    exact ⟨x, xm⟩
  · rintro ⟨x, xm⟩
    obtain ⟨y, base, _⟩ := R.slice_has_base xm
    exact ⟨y, base⟩

/-- Progress below the requested length is witnessed by a nonempty inverse
label. The ancestor invariant, not just language membership, is needed here. -/
theorem ancestor_progress {n : ℕ} {y : Word α} (ancestor : y ∈ R.ancestors n)
    (short : y.length < n) :
    ∃ w, w ≠ [] ∧ (R.inverseFibre n y w).Nonempty := by
  obtain ⟨ym, x, xm, path⟩ := R.mem_ancestors_iff.mp ancestor
  rcases path.cases_tail with rfl | ⟨z, initialPath, step⟩
  · have := xm.2
    omega
  · have zm := R.step_mem step ym
    have za : z ∈ R.ancestors n := R.mem_ancestors_iff.mpr ⟨zm, x, xm, initialPath⟩
    obtain ⟨w, positive, length, reduction⟩ := step
    refine ⟨w, ?_, z, za, reduction, length⟩
    intro empty
    simp [empty] at length
    omega

/-- A nonempty-label inverse call strictly increases certificate length. -/
theorem inverse_rank_lt {n : ℕ} {y w x : Word α} (nonempty : w ≠ [])
    (member : x ∈ R.inverseFibre n y w) : R.rank y < R.rank x := by
  apply R.step_rank_lt
  have length := member.2.2
  exact ⟨w, by have := List.length_pos_iff.mpr nonempty; omega, length, member.2.1⟩

end ComplexityOfGenerators.SelfReduction
