import Mathlib.Logic.Relation
import Mathlib.Data.Set.Card
import Mathlib.Data.Fintype.Basic

/-!
# Bounded reachability and the midpoint recursion

This module supplies the finite-relation interface needed for the native
configuration graph: cardinality bounds the necessary path length, and midpoint
recursion tests paths of length at most `2^depth`. `SavitchStack` connects this
relation to Complexitylib's machine-independent stack evaluator; the library's
machine-level containment theorem is specialized to its own Turing machines.

The Boolean recursion is an algorithm specification. No native space bound is
inferred from its Lean evaluation or from storing a set of reachable vertices.
-/

namespace ComplexityOfGenerators.FiniteReachability

variable {V : Type} (edge : V → V → Prop)

/-- Reachability in at most the given number of edges, including a zero-edge
path. This definition is used only to state and prove the search specification. -/
def Within : ℕ → V → V → Prop
  | 0, a, b => a = b
  | n + 1, a, b => Within n a b ∨ ∃ c, Within n a c ∧ edge c b

theorem within_succ {n : ℕ} {a b : V} (path : Within edge n a b) :
    Within edge (n + 1) a b := Or.inl path

theorem within_mono {m n : ℕ} (bound : m ≤ n) {a b : V}
    (path : Within edge m a b) : Within edge n a b := by
  induction bound with
  | refl => exact path
  | step bound ih => exact within_succ edge ih

theorem within_refl (n : ℕ) (a : V) : Within edge n a a :=
  within_mono edge (Nat.zero_le n) rfl

theorem within_add (m n : ℕ) (a b : V) :
    Within edge (m + n) a b ↔ ∃ c, Within edge m a c ∧ Within edge n c b := by
  induction n generalizing b with
  | zero => simp [Within]
  | succ n ih =>
      simp only [Within]
      constructor
      · rintro (path | ⟨last, path, step⟩)
        · obtain ⟨mid, left, right⟩ := (ih b).mp path
          exact ⟨mid, left, Or.inl right⟩
        · obtain ⟨mid, left, right⟩ := (ih last).mp path
          exact ⟨mid, left, Or.inr ⟨last, right, step⟩⟩
      · rintro ⟨mid, left, right | ⟨last, right, step⟩⟩
        · exact Or.inl ((ih b).mpr ⟨mid, left, right⟩)
        · exact Or.inr ⟨last, (ih last).mpr ⟨mid, left, right⟩, step⟩

theorem within_path {n : ℕ} {a b : V} (path : Within edge n a b) :
    Relation.ReflTransGen edge a b := by
  induction n generalizing b with
  | zero => cases path; exact .refl
  | succ n ih =>
      rcases path with shorter | ⟨last, initialPath, step⟩
      · exact ih shorter
      · exact (ih initialPath).tail step

theorem path_within {a b : V} (path : Relation.ReflTransGen edge a b) :
    ∃ n, Within edge n a b := by
  induction path with
  | refl => exact ⟨0, rfl⟩
  | tail path step ih =>
      obtain ⟨n, initialPath⟩ := ih
      exact ⟨n + 1, Or.inr ⟨_, initialPath, step⟩⟩

private theorem within_stable {a : V} {n : ℕ}
    (stable : ∀ b, Within edge (n + 1) a b → Within edge n a b) :
    ∀ k b, Within edge (n + k) a b → Within edge n a b := by
  intro k
  induction k with
  | zero => exact fun _ path => path
  | succ k ih =>
      intro b path
      rcases path with shorter | ⟨last, initialPath, step⟩
      · exact ih b shorter
      · exact stable b (Or.inr ⟨last, ih last initialPath, step⟩)

/-- A finite graph's successor closure stabilizes within its vertex count.
This is a counting argument; it does not store that closure in a work tape. -/
theorem exists_stable [Fintype V] (a : V) :
    ∃ n ≤ Fintype.card V, ∀ b, Within edge (n + 1) a b → Within edge n a b := by
  classical
  by_contra unstabilized
  have grows (n : ℕ) (small : n ≤ Fintype.card V) :
      {b | Within edge n a b} ⊂ {b | Within edge (n + 1) a b} := by
    refine ⟨fun _ path => within_succ edge path, ?_⟩
    exact fun stable => unstabilized ⟨n, small, stable⟩
  have count (n : ℕ) (small : n ≤ Fintype.card V) :
      n + 1 ≤ ({b | Within edge n a b} : Set V).ncard := by
    induction n with
    | zero => simp [Within]
    | succ n ih =>
        have previous := ih (by omega)
        have increase := Set.ncard_lt_ncard (grows n (by omega)) (Set.toFinite _)
        omega
  have upper := Set.ncard_le_ncard
    (Set.subset_univ {b | Within edge (Fintype.card V) a b}) (Set.finite_univ)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at upper
  have lower := count (Fintype.card V) le_rfl
  omega

theorem path_iff_within [Fintype V] (n : ℕ) (large : Fintype.card V ≤ n) (a b : V) :
    Relation.ReflTransGen edge a b ↔ Within edge n a b := by
  refine ⟨?_, within_path edge⟩
  intro path
  obtain ⟨t, path⟩ := path_within edge path
  obtain ⟨s, bound, stable⟩ := exists_stable edge a
  by_cases early : t ≤ n
  · exact within_mono edge early path
  · have after : s ≤ t := by omega
    have shortened := within_stable edge stable (t - s) b
    rw [Nat.add_sub_of_le after] at shortened
    exact within_mono edge (bound.trans large) (shortened path)

/-- Removing cycles needs at most one fewer edge than there are vertices.
This sharper bound permits an acceptance leaf that tests only its own vertex. -/
theorem exists_stable_strict [Fintype V] (a : V) :
    ∃ n < Fintype.card V, ∀ b, Within edge (n + 1) a b → Within edge n a b := by
  classical
  by_contra unstabilized
  have grows (n : ℕ) (small : n < Fintype.card V) :
      {b | Within edge n a b} ⊂ {b | Within edge (n + 1) a b} := by
    refine ⟨fun _ path => within_succ edge path, ?_⟩
    exact fun stable => unstabilized ⟨n, small, stable⟩
  have count (n : ℕ) (small : n ≤ Fintype.card V) :
      n + 1 ≤ ({b | Within edge n a b} : Set V).ncard := by
    induction n with
    | zero => simp [Within]
    | succ n ih =>
        have previous := ih (by omega)
        have increase := Set.ncard_lt_ncard (grows n (by omega)) (Set.toFinite _)
        omega
  have upper := Set.ncard_le_ncard
    (Set.subset_univ {b | Within edge (Fintype.card V) a b}) (Set.finite_univ)
  rw [Set.ncard_univ, Nat.card_eq_fintype_card] at upper
  have lower := count (Fintype.card V) le_rfl
  omega

theorem path_iff_within_pred [Fintype V] (n : ℕ)
    (large : Fintype.card V ≤ n + 1) (a b : V) :
    Relation.ReflTransGen edge a b ↔ Within edge n a b := by
  refine ⟨?_, within_path edge⟩
  intro path
  obtain ⟨t, path⟩ := path_within edge path
  obtain ⟨s, bound, stable⟩ := exists_stable_strict edge a
  by_cases early : t ≤ n
  · exact within_mono edge early path
  · have after : s ≤ t := by omega
    have shortened := within_stable edge stable (t - s) b
    rw [Nat.add_sub_of_le after] at shortened
    exact within_mono edge (by omega) (shortened path)

section Algorithm

variable [Fintype V] [DecidableEq V] [DecidableRel edge]

/-- Savitch's midpoint test. The depth controls path length exponentially;
midpoints range over the fixed finite vertex type. -/
def search : ℕ → V → V → Bool
  | 0, a, b => decide (a = b ∨ edge a b)
  | depth + 1, a, b => decide (∃ mid,
      search depth a mid = true ∧ search depth mid b = true)

theorem search_correct (depth : ℕ) (a b : V) :
    search edge depth a b = true ↔ Within edge (2 ^ depth) a b := by
  induction depth generalizing a b with
  | zero => simp [search, Within]
  | succ depth ih =>
      rw [pow_succ, Nat.mul_two, within_add]
      simp only [search, decide_eq_true_eq, ih]

theorem search_iff_path (depth : ℕ) (large : Fintype.card V ≤ 2 ^ depth) (a b : V) :
    search edge depth a b = true ↔ Relation.ReflTransGen edge a b := by
  rw [search_correct, path_iff_within edge (2 ^ depth) large]

end Algorithm
end ComplexityOfGenerators.FiniteReachability
