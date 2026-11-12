import ComplexityOfGenerators.Proofs.OriginalSourceClosureSupport

/-! Wordwise lucky source paths for binary direct-call constructions. The
same polynomial bounds both source indices and both source runtimes as a
function of the final output length; no per-layer witness premise is used. -/
namespace ComplexityOfGenerators.OriginalSourceClosure
noncomputable section
variable {α : Type} [Fintype α]

private theorem enlarge_path (G : UniformGenerators α) (p q : PolynomialBound)
    (dominate : ∀ m,p m≤q m) (word : List α) (m : ℕ) (length : word.length≤m)
    (index : ℕ) (small : index≤p word.length) (bits : BitString)
    (run : G.machine.run (generatorData index) bits (p word.length)=.halted (.accepted word)) :
    index≤q m ∧ G.machine.run (generatorData index) bits (q m)=.halted (.accepted word) := by
  have time := (dominate word.length).trans (q.monotone length)
  refine ⟨small.trans time,?_⟩
  have padded := G.machine.run_halted_add (generatorData index) bits (p word.length) (.accepted word) run
    (q m-p word.length)
  rwa [Nat.add_sub_of_le time] at padded

theorem binary_bounded_witnesses (families : Bool → UniformGenerators α)
    (fast : ∀ tag,(families tag).GlobalWordPolynomialTime) :
    ∃ q : PolynomialBound,∀ tag,∀ word∈(families tag).language,∀ m,word.length≤m →
      ∃ index,index≤q m ∧ ∃ bits : BitString,bits≠[] ∧
        (families tag).machine.run (generatorData index) bits (q m)=.halted (.accepted word) := by
  obtain ⟨left,leftPaths⟩ := (fast false).bounded_witnesses
  obtain ⟨right,rightPaths⟩ := (fast true).bounded_witnesses
  let q := left.add right
  have leftBound (m : ℕ) : left m≤q m := (Nat.le_add_right _ _).trans (left.add_le right m)
  have rightBound (m : ℕ) : right m≤q m := (Nat.le_add_left _ _).trans (left.add_le right m)
  refine ⟨q,?_⟩
  intro tag word member m length
  cases tag
  · obtain ⟨index,small,bits,nonempty,run⟩ := leftPaths word member
    obtain ⟨small,run⟩ := enlarge_path (families false) left q leftBound word m length index small bits run
    exact ⟨index,small,bits,nonempty,run⟩
  · obtain ⟨index,small,bits,nonempty,run⟩ := rightPaths word member
    obtain ⟨small,run⟩ := enlarge_path (families true) right q rightBound word m length index small bits run
    exact ⟨index,small,bits,nonempty,run⟩

theorem concat_fast_witnesses (families : Bool → UniformGenerators α)
    (fast : ∀ tag,(families tag).GlobalWordPolynomialTime) :
    ∃ q : PolynomialBound,∀ word∈IndexedSupport.concat (families false).language (families true).language,
      ∃ u v : List α,∃ i j : ℕ,∃ leftBits rightBits : BitString,
        u++v=word ∧ i+j≤(q.add q) word.length ∧ leftBits≠[] ∧ rightBits≠[] ∧
        (families false).machine.run (generatorData i) leftBits (q word.length)=.halted (.accepted u) ∧
        (families true).machine.run (generatorData j) rightBits (q word.length)=.halted (.accepted v) := by
  obtain ⟨q,paths⟩ := binary_bounded_witnesses families fast
  refine ⟨q,?_⟩
  rintro word ⟨u,left,v,right,equal⟩
  have leftLength : u.length≤word.length := by rw [←equal,List.length_append]; omega
  have rightLength : v.length≤word.length := by rw [←equal,List.length_append]; omega
  obtain ⟨i,leftIndex,leftBits,leftNonempty,leftRun⟩ := paths false u left word.length leftLength
  obtain ⟨j,rightIndex,rightBits,rightNonempty,rightRun⟩ := paths true v right word.length rightLength
  exact ⟨u,v,i,j,leftBits,rightBits,equal,
    (Nat.add_le_add leftIndex rightIndex).trans (q.add_le q word.length),leftNonempty,rightNonempty,leftRun,rightRun⟩

end
end ComplexityOfGenerators.OriginalSourceClosure
