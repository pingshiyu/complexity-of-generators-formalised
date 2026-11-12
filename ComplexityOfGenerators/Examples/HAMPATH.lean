import ComplexityOfGenerators.SelfReducibility
import Mathlib.Data.Nat.Log

/-!
# Concrete adjacency-matrix HAMPATH instances

The word codec and vertex insertion/deletion below are the ones used by the
manuscript. This is the semantic layer; no native-machine implementation is
assumed and no `PG` membership theorem is asserted here. Later modules prove
the parser/codec round trip, binary certificate blocks, the full all-word
self-reduction, ancestor/base characterizations and exact insertion fibres.
`HAMPATHBaseNative` supplies the native polynomial base family, including
empty target indices. `HAMPATHNative` supplies total polynomial syntax, rank
and label-width machines, together with the complete forward reduction.
The complete native verifier and incident-edge inverse insertion are checked,
including exact generated fibres and uniform transition/seed bounds.
`HAMPATHNative.ExactRecursive` assembles exact recursive generability and the
resulting native polynomial generator.
-/

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

inductive Symbol
  | bit (value : Bool)
  | separator
  deriving DecidableEq, Fintype

/-- Edges outside `[size]` are canonically false. -/
structure Graph where
  size : ℕ
  edge : ℕ → ℕ → Bool
  outside : ∀ v w, size ≤ v ∨ size ≤ w → edge v w = false
  loopFree : ∀ v, edge v v = false

def Graph.encode (G : Graph) (start : ℕ) : List Symbol :=
  List.replicate G.size (.bit true) ++ [.separator] ++
    (List.range G.size).flatMap (fun v =>
      (List.range G.size).map (fun w => .bit (G.edge v w))) ++
    [.separator] ++ (List.range G.size).map (fun v => .bit (decide (v = start)))

def encodingLength (k : ℕ) : ℕ := k * k + 2 * k + 2

theorem Graph.encode_length (G : Graph) (start : ℕ) :
    (G.encode start).length = encodingLength G.size := by
  have matrix : ((List.range G.size).flatMap (fun v =>
      (List.range G.size).map (fun w => Symbol.bit (G.edge v w)))).length =
      G.size * G.size := by
    simp [List.length_flatMap]
  simp only [Graph.encode, List.length_append, List.length_replicate,
    List.length_singleton, List.length_map, List.length_range, matrix, encodingLength]
  omega

/-- Insertion at label `s` shifts later labels by one. -/
def expand (s v : ℕ) : ℕ := if v < s then v else v + 1

/-- Deletion uses the order-preserving relabelling of the paper. -/
def contract (s v : ℕ) : ℕ := if v < s then v else v - 1

theorem expand_ne (s v : ℕ) : expand s v ≠ s := by
  unfold expand
  split <;> omega

@[simp] theorem contract_expand (s v : ℕ) : contract s (expand s v) = v := by
  unfold expand contract
  split_ifs <;> omega

theorem expand_contract {s v : ℕ} (different : v ≠ s) :
    expand s (contract s v) = v := by
  unfold expand contract
  split_ifs <;> omega

theorem expand_injective (s : ℕ) : Function.Injective (expand s) := by
  intro v w equal
  simpa using congrArg (contract s) equal

theorem expand_lt {k s v : ℕ} (h : v < k) : expand s v < k + 1 := by
  unfold expand
  split <;> omega

theorem expand_lt_iff {k s v : ℕ} (hs : s ≤ k) :
    expand s v < k + 1 ↔ v < k := by
  unfold expand
  split <;> omega

theorem contract_lt {k s v : ℕ} (hs : s < k + 1) (hv : v < k + 1)
    (different : v ≠ s) : contract s v < k := by
  unfold contract
  split <;> omega

def Graph.delete (G : Graph) (s : ℕ) : Graph where
  size := G.size - 1
  edge := fun v w => if v < G.size - 1 ∧ w < G.size - 1 then
    G.edge (expand s v) (expand s w) else false
  outside := by
    intro v w h
    have notInside : ¬ (v < G.size - 1 ∧ w < G.size - 1) := by
      rcases h with h | h <;> omega
    simp only [ite_eq_right notInside]
  loopFree := by
    intro v
    split_ifs
    · exact G.loopFree _
    · rfl

/-- The incoming and outgoing rows are precisely the independent incident-edge
choices of the generator; the diagonal is always forced to zero. -/
def Graph.insert (G : Graph) (s : ℕ) (incoming outgoing : ℕ → Bool) : Graph where
  size := G.size + 1
  edge := fun v w =>
    if v < G.size + 1 ∧ w < G.size + 1 ∧ v ≠ w then
      if v = s then outgoing (contract s w)
      else if w = s then incoming (contract s v)
      else G.edge (contract s v) (contract s w)
    else false
  outside := by
    intro v w h
    have notInside : ¬ (v < G.size + 1 ∧ w < G.size + 1 ∧ v ≠ w) := by
      rcases h with h | h <;> omega
    simp only [ite_eq_right notInside]
  loopFree := by intro v; simp

theorem Graph.insert_edge_expanded (G : Graph) {s : ℕ} (hs : s ≤ G.size)
    (incoming outgoing : ℕ → Bool) (v w : ℕ) :
    (G.insert s incoming outgoing).edge (expand s v) (expand s w) = G.edge v w := by
  by_cases hv : v < G.size
  · by_cases hw : w < G.size
    · by_cases equal : v = w
      · subst w
        simp [Graph.insert, G.loopFree]
      · have neq : expand s v ≠ expand s w := fun h => equal (expand_injective s h)
        have hv' : expand s v ≤ G.size := by have := expand_lt (s := s) hv; omega
        have hw' : expand s w ≤ G.size := by have := expand_lt (s := s) hw; omega
        simp [Graph.insert, hv', hw', neq,
          expand_ne, contract_expand]
    · have outside : G.edge v w = false := G.outside v w (Or.inr (by omega))
      have notInside : ¬ expand s w < G.size + 1 := by
        rw [expand_lt_iff hs]; exact hw
      have bad : ¬ expand s w ≤ G.size := by omega
      simp [Graph.insert, bad, outside]
  · have outside : G.edge v w = false := G.outside v w (Or.inl (by omega))
    have notInside : ¬ expand s v < G.size + 1 := by
      rw [expand_lt_iff hs]; exact hv
    have bad : ¬ expand s v ≤ G.size := by omega
    simp [Graph.insert, bad, outside]

theorem Graph.delete_insert_edges (G : Graph) {s : ℕ} (hs : s ≤ G.size)
    (incoming outgoing : ℕ → Bool) (v w : ℕ) :
    ((G.insert s incoming outgoing).delete s).edge v w = G.edge v w := by
  by_cases hv : v < G.size
  · by_cases hw : w < G.size
    · simpa [Graph.delete, Graph.insert, hv, hw] using
        G.insert_edge_expanded hs incoming outgoing v w
    · simp [Graph.delete, Graph.insert, hw, G.outside v w (Or.inr (by omega))]
  · simp [Graph.delete, Graph.insert, hv, G.outside v w (Or.inl (by omega))]

def Follows (edge : ℕ → ℕ → Bool) : List ℕ → Prop
  | [] => True
  | [_] => True
  | v :: w :: rest => edge v w = true ∧ Follows edge (w :: rest)

def HamiltonianFrom (G : Graph) (start : ℕ) : Prop :=
  ∃ path : List ℕ, path.head? = some start ∧ path.Nodup ∧
    (∀ v, v ∈ path ↔ v < G.size) ∧ Follows G.edge path

/-- The concrete adjacency-matrix language with a specified start vertex. -/
def language : Language Symbol :=
  {word | ∃ G start, HamiltonianFrom G start ∧ G.encode start = word}

theorem follows_map {e e' : ℕ → ℕ → Bool} (f : ℕ → ℕ)
    (respects : ∀ v w, e' (f v) (f w) = e v w) (path : List ℕ) :
    Follows e' (path.map f) ↔ Follows e path := by
  induction path with
  | nil => trivial
  | cons v rest ih =>
    cases rest with
    | nil => trivial
    | cons w rest =>
      simp only [List.map_cons, Follows, respects]
      exact and_congr Iff.rfl (by simpa only [List.map_cons] using ih)

theorem prepend_preserves_hamiltonian (G : Graph) {start s : ℕ}
    (hs : s ≤ G.size) (incoming outgoing : ℕ → Bool) (required : outgoing start = true)
    (path : HamiltonianFrom G start) :
    HamiltonianFrom (G.insert s incoming outgoing) s := by
  obtain ⟨vertices, head, nodup, covers, follows⟩ := path
  have startBound : start < G.size := by
    cases vertices with
    | nil => simp at head
    | cons v rest =>
      have equal : v = start := by simpa using head
      subst v
      exact (covers start).mp (by simp)
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
      · subst v; exact Nat.lt_succ_of_le hs
      · obtain ⟨w, sourceMember, rfl⟩ := List.mem_map.mp member
        exact expand_lt ((covers w).mp sourceMember)
    · intro bound
      by_cases equal : v = s
      · exact List.mem_cons.mpr (Or.inl equal)
      · apply List.mem_cons.mpr
        right
        exact List.mem_map.mpr ⟨contract s v,
          (covers _).mpr (contract_lt (Nat.lt_succ_of_le hs) bound equal),
          expand_contract equal⟩
  · have transferred := (follows_map (expand s)
      (G.insert_edge_expanded hs incoming outgoing) vertices).mpr follows
    cases vertices with
    | nil => simp at head
    | cons v rest =>
      have equal : v = start := by simpa using head
      subst v
      change (G.insert s incoming outgoing).edge s (expand s start) = true ∧ _
      constructor
      · have bound : expand s start ≤ G.size := by
          have := expand_lt (s := s) startBound; omega
        simp [Graph.insert, hs, bound,
          Ne.symm (expand_ne s start), required]
      · exact transferred

def width (k : ℕ) : ℕ := Nat.clog 2 k

def rank (k : ℕ) : ℕ := ∑ j ∈ Finset.range k, width (j + 1)

@[simp] theorem rank_zero : rank 0 = 0 := by simp [rank]
@[simp] theorem rank_succ (k : ℕ) : rank (k + 1) = rank k + width (k + 1) := by
  simp [rank, Finset.sum_range_succ]

theorem width_le_size (k : ℕ) : width k ≤ k := by
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))

theorem width_log_bound (k : ℕ) : width k ≤ Nat.log 2 k + 1 := by
  exact Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_succ_log_self (by decide) k))

theorem rank_le_square (k : ℕ) : rank k ≤ k * k := by
  calc
    rank k ≤ ∑ _j ∈ Finset.range k, k := by
      apply Finset.sum_le_sum
      intro j hj
      exact (width_le_size (j + 1)).trans (by have := Finset.mem_range.mp hj; omega)
    _ = k * k := by simp

theorem rank_delete (k : ℕ) (positive : 0 < k) :
    rank (k - 1) = rank k - width k := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
  simp [rank_succ]

end ComplexityOfGenerators.Examples.HAMPATH
