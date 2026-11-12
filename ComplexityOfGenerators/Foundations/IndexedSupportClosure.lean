import ComplexityOfGenerators.ExpectedGenerators
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

/-!
# Support and producing-index bounds for the positive operations

These are the extensional obligations in the proof of Proposition 6.3. They do
not assert that a native machine implementing the operations has been compiled.
Zero-index outputs must be empty words in the expected-length setting; that
operational fact is proved separately in `ExpectedClosureBounds`.
-/

namespace ComplexityOfGenerators.IndexedSupport

variable {α : Type}

abbrev Layers (α : Type) := ℕ → Language α

def language (G : Layers α) : Language α := {w | ∃ i, w ∈ G i}

def CoveredBy (G : Layers α) (q : PolynomialBound) : Prop :=
  ∀ w ∈ language G, ∃ i, i ≤ q w.length ∧ w ∈ G i

def concat (L K : Language α) : Language α :=
  {w | ∃ u ∈ L, ∃ v ∈ K, u ++ v = w}

/-- Empty factors can be omitted from a finite concatenation. -/
def star (L : Language α) : Language α :=
  {w | ∃ words : List (List α), (∀ u ∈ words, u ∈ L ∧ u ≠ []) ∧ words.flatten = w}

def unionLayers (G H : Layers α) (n : ℕ) : Language α := G n ∪ H n

def concatLayers (G H : Layers α) (n : ℕ) : Language α :=
  {w | ∃ i j, i + j = n ∧ ∃ u ∈ G i, ∃ v ∈ H j, u ++ v = w}

def starLayers (G : Layers α) (n : ℕ) : Language α :=
  {w | ∃ indices : List ℕ, ∃ words : List (List α),
    List.Forall₂ (fun i u => 0 < i ∧ u ∈ G i) indices words ∧
    indices.sum = n ∧ words.flatten = w}

@[simp] theorem union_language (G H : Layers α) :
    language (unionLayers G H) = language G ∪ language H := by
  ext w
  constructor
  · rintro ⟨i, member | member⟩
    · exact Or.inl ⟨i, member⟩
    · exact Or.inr ⟨i, member⟩
  · rintro (⟨i, member⟩ | ⟨i, member⟩)
    · exact ⟨i, Or.inl member⟩
    · exact ⟨i, Or.inr member⟩

@[simp] theorem concat_language (G H : Layers α) :
    language (concatLayers G H) = concat (language G) (language H) := by
  ext w
  constructor
  · rintro ⟨n, i, j, _, u, hu, v, hv, rfl⟩
    exact ⟨u, ⟨i, hu⟩, v, ⟨j, hv⟩, rfl⟩
  · rintro ⟨u, ⟨i, hu⟩, v, ⟨j, hv⟩, rfl⟩
    exact ⟨i + j, i, j, rfl, u, hu, v, hv, rfl⟩

theorem union_coverage (G H : Layers α) (q : PolynomialBound)
    (left : CoveredBy G q) (right : CoveredBy H q) : CoveredBy (unionLayers G H) q := by
  intro w member
  rw [union_language] at member
  rcases member with member | member
  · obtain ⟨i, bound, generated⟩ := left w member
    exact ⟨i, bound, Or.inl generated⟩
  · obtain ⟨i, bound, generated⟩ := right w member
    exact ⟨i, bound, Or.inr generated⟩

theorem concat_coverage (G H : Layers α) (q : PolynomialBound)
    (left : CoveredBy G q) (right : CoveredBy H q) :
    CoveredBy (concatLayers G H) (q.add q) := by
  intro w member
  rw [concat_language] at member
  obtain ⟨u, hu, v, hv, rfl⟩ := member
  obtain ⟨i, hi, generatedU⟩ := left u hu
  obtain ⟨j, hj, generatedV⟩ := right v hv
  refine ⟨i + j, ?_, i, j, rfl, u, generatedU, v, generatedV, rfl⟩
  apply (Nat.add_le_add (hi.trans (q.monotone (show u.length ≤ (u ++ v).length by simp)))
    (hj.trans (q.monotone (show v.length ≤ (u ++ v).length by simp)))).trans
  exact q.add_le q (u ++ v).length

/-- At most one index is needed per symbol after empty factors are omitted. -/
theorem factors_count_le_length (words : List (List α))
    (positive : ∀ u ∈ words, u ≠ []) : words.length ≤ words.flatten.length := by
  induction words with
  | nil => simp
  | cons u rest ih =>
    have hu : 0 < u.length := List.length_pos_iff.mpr (positive u (by simp))
    have hr := ih (by intro v hv; exact positive v (by simp [hv]))
    simp only [List.length_cons, List.flatten_cons, List.length_append]
    omega

theorem factor_length_le (words : List (List α)) (u : List α) (member : u ∈ words) :
    u.length ≤ words.flatten.length := by
  induction words with
  | nil => simp at member
  | cons v rest ih =>
    simp only [List.mem_cons] at member
    rcases member with rfl | member
    · simp
    · exact (ih member).trans (by simp)

/-- Choose producing indices for all factors, retaining a sum bound. -/
theorem choose_factor_indices (G : Layers α) (q : PolynomialBound)
    (coverage : CoveredBy G q) (zero : ∀ u ∈ G 0, u = []) (m : ℕ)
    (words : List (List α))
    (members : ∀ u ∈ words, u ∈ language G ∧ u ≠ [] ∧ u.length ≤ m) :
    ∃ indices : List ℕ,
      List.Forall₂ (fun i u => 0 < i ∧ u ∈ G i) indices words ∧
      indices.sum ≤ words.length * q m := by
  induction words with
  | nil => exact ⟨[], .nil, by simp⟩
  | cons u rest ih =>
    have hu := members u (by simp)
    obtain ⟨i, bound, generated⟩ := coverage u hu.1
    have positive : 0 < i := by
      by_contra absent
      have eq : i = 0 := by omega
      subst i
      exact hu.2.1 (zero u generated)
    obtain ⟨indices, generatedRest, restBound⟩ := ih (by
      intro v hv; exact members v (by simp [hv]))
    refine ⟨i :: indices, .cons ⟨positive, generated⟩ generatedRest, ?_⟩
    have hi := bound.trans (q.monotone hu.2.2)
    simp only [List.sum_cons, List.length_cons]
    nlinarith

/-- A polynomial dominating `m*q(m)`, including the empty-word boundary. -/
def starBound (q : PolynomialBound) : PolynomialBound :=
  ⟨q.coefficient, q.degree + 1, q.coefficient_pos⟩

theorem starBound_ge (q : PolynomialBound) (m : ℕ) : m * q m ≤ starBound q m := by
  simp only [starBound, PolynomialBound.eval, pow_succ]
  nlinarith [Nat.mul_le_mul_left (q.coefficient * (m + 1) ^ q.degree) (Nat.le_succ m)]

theorem star_coverage (G : Layers α) (q : PolynomialBound)
    (coverage : CoveredBy G q) (zero : ∀ u ∈ G 0, u = []) :
    ∀ w ∈ star (language G), ∃ n, n ≤ starBound q w.length ∧ w ∈ starLayers G n := by
  rintro w ⟨words, members, rfl⟩
  obtain ⟨indices, generated, bound⟩ := choose_factor_indices G q coverage zero words.flatten.length words
    (by intro u hu; exact ⟨(members u hu).1, (members u hu).2, factor_length_le words u hu⟩)
  refine ⟨indices.sum, ?_, indices, words, generated, rfl, rfl⟩
  exact bound.trans ((Nat.mul_le_mul_right _ (factors_count_le_length words
    (fun u hu => (members u hu).2))).trans (starBound_ge q words.flatten.length))

end ComplexityOfGenerators.IndexedSupport
