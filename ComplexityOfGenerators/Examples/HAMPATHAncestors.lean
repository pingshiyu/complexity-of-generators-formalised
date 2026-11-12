import ComplexityOfGenerators.Examples.HAMPATHSelfReduction
import ComplexityOfGenerators.Proofs.SelfReduction

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

/-- A concrete one-vertex extension, forcing just the edge to the previous
start. It witnesses reachability from every larger productive target size. -/
def prependGraph (G : Graph) (start : ℕ) : Graph :=
  G.insert 0 (fun _ => false) (fun v => decide (v = start))

theorem prependGraph_hamiltonian (G : Graph) (start : ℕ)
    (member : HamiltonianFrom G start) : HamiltonianFrom (prependGraph G start) 0 :=
  prepend_preserves_hamiltonian G (Nat.zero_le _) _ _ (by simp) member

theorem prependGraph_delete (G : Graph) (start : ℕ) :
    (prependGraph G start).delete 0 = G := by
  apply Graph.ext
  · simp [prependGraph, Graph.insert, Graph.delete]
  · exact G.delete_insert_edges (Nat.zero_le _) _ _

theorem prependGraph_step (G : Graph) (start : ℕ) (member : HamiltonianFrom G start) :
    selfReduction.Step ((prependGraph G start).encode 0) (G.encode start) := by
  have originalBound := member.start_bound
  have startBound : 0 < (prependGraph G start).size := by simp [prependGraph, Graph.insert]
  have large : 2 ≤ (prependGraph G start).size := by
    change 2 ≤ G.size + 1
    omega
  have nextBound : expand 0 start < (prependGraph G start).size := expand_lt originalBound
  have different : expand 0 start ≠ 0 := expand_ne _ _
  have edge : (prependGraph G start).edge 0 (expand 0 start) = true := by
    have numericBound : expand 0 start ≤ G.size := by
      change expand 0 start < G.size + 1 at nextBound
      omega
    simp [prependGraph, Graph.insert, numericBound, Ne.symm different,
      contract_expand]
  refine ⟨vertexLabel (prependGraph G start).size (expand 0 start), ?_, ?_, ?_⟩
  · change 0 < wordWidth _
    rw [wordWidth_encode _ _ startBound]
    exact Nat.clog_pos (by decide) (by omega)
  · change (vertexLabel _ _).length = wordWidth _
    rw [vertexLabel_length, wordWidth_encode _ _ startBound]
  · change wordReduce _ _ = _
    rw [wordReduce_encode_label _ _ _ startBound large nextBound different edge,
      prependGraph_delete, contract_expand]

theorem exists_extension_path (G : Graph) (start : ℕ) (member : HamiltonianFrom G start)
    (M : ℕ) (bound : G.size ≤ M) :
    ∃ H source, HamiltonianFrom H source ∧ H.size = M ∧
      selfReduction.Path (H.encode source) (G.encode start) := by
  induction M, bound using Nat.le_induction with
  | base => exact ⟨G, start, member, rfl, .refl⟩
  | succ M bound ih =>
    obtain ⟨H, source, member', size, path⟩ := ih
    refine ⟨prependGraph H source, 0, prependGraph_hamiltonian H source member', ?_, ?_⟩
    · change H.size + 1 = M + 1
      omega
    · exact path.head (prependGraph_step H source member')

theorem encodingLength_strictMono : StrictMono encodingLength := by
  intro k m less
  unfold encodingLength
  have square : k * k ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
  omega

/-- At target length f(M), the ancestor language consists of exactly the
Hamiltonian instances with at most M vertices, as claimed in the appendix. -/
theorem ancestors_eq (M : ℕ) :
    selfReduction.ancestors (encodingLength M) =
      {word | ∃ G start, HamiltonianFrom G start ∧ G.size ≤ M ∧ G.encode start = word} := by
  ext word
  constructor
  · intro ancestor
    obtain ⟨G, start, member, equal⟩ := ancestor.1
    have length := selfReduction.ancestor_length_le ancestor
    rw [← equal, G.encode_length] at length
    have size : G.size ≤ M := by
      by_contra contrary
      have strict := encodingLength_strictMono (by omega : M < G.size)
      omega
    exact ⟨G, start, member, size, equal⟩
  · rintro ⟨G, start, member, bound, rfl⟩
    obtain ⟨H, source, sourceMember, size, path⟩ := exists_extension_path G start member M bound
    apply selfReduction.mem_ancestors_iff.mpr
    exact ⟨⟨G, start, member, rfl⟩, H.encode source,
      ⟨⟨H, source, sourceMember, rfl⟩, by rw [H.encode_length, size]⟩, path⟩

/-- Every productive target uses the same singleton base. The zero-vertex
target has no Hamiltonian instances and therefore no bases. -/
theorem bases_eq (M : ℕ) :
    selfReduction.bases (encodingLength M) =
      {word | 1 ≤ M ∧ word = singleton.encode 0} := by
  ext word
  change (word ∈ selfReduction.ancestors (encodingLength M) ∧ wordRank word = 0) ↔ _
  rw [ancestors_eq]
  constructor
  · rintro ⟨⟨G, start, member, bound, equal⟩, zero⟩
    rw [← equal, wordRank_encode G start member.start_bound] at zero
    obtain ⟨rfl, rfl⟩ := rank_zero_graph G member zero
    exact ⟨bound, equal.symm⟩
  · rintro ⟨bound, rfl⟩
    exact ⟨⟨singleton, 0, singleton_hamiltonian, bound, rfl⟩,
      by rw [wordRank_encode singleton 0 singleton_hamiltonian.start_bound]; exact singleton_rank⟩

/-- A target length outside the adjacency-matrix length polynomial has no
target instances and hence no ancestor or base outputs. -/
theorem ancestors_eq_empty_of_nonencodingLength (n : ℕ)
    (nonencoding : ∀ M, n ≠ encodingLength M) : selfReduction.ancestors n = ∅ := by
  ext word
  constructor
  · intro ancestor
    exfalso
    obtain ⟨_, source, ⟨⟨G, start, _, equal⟩, length⟩, _⟩ :=
      selfReduction.mem_ancestors_iff.mp ancestor
    apply nonencoding G.size
    rw [← equal, G.encode_length] at length
    exact length.symm
  · intro empty
    exact False.elim empty

end ComplexityOfGenerators.Examples.HAMPATH
