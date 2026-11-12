import ComplexityOfGenerators.Foundations.IndexedStarLanguage
import ComplexityOfGenerators.Foundations.ExpectedClosureBounds
import ComplexityOfGenerators.Proofs.ExpectedLengthContainment

/-! Support, active-index and wordwise witness bounds for direct-source
closure constructions. None of these lemmas presumes an implementation of the
closure generator or a short path for every word in every source layer. -/
namespace ComplexityOfGenerators
noncomputable section
variable {α : Type} [Fintype α]

namespace IndexedSupport

def active (G : Layers α) : Set ℕ := {n | (G n).Nonempty}

theorem union_active_infinite (G H : Layers α) (infinite : (active G).Infinite) :
    (active (unionLayers G H)).Infinite := by
  apply infinite.mono
  rintro n ⟨word,member⟩
  exact ⟨word,Or.inl member⟩

theorem concat_active_infinite (G H : Layers α) (infinite : (active G).Infinite)
    (j : ℕ) (right : (H j).Nonempty) : (active (concatLayers G H)).Infinite := by
  have image : ((fun i : ℕ => i+j) '' active G).Infinite :=
    infinite.image (by intro a _ b _ same; dsimp at same; omega)
  apply image.mono
  rintro n ⟨i,⟨u,left⟩,rfl⟩
  obtain ⟨v,right⟩ := right
  exact ⟨u++v,i,j,rfl,u,left,v,right,rfl⟩

theorem star_active_infinite (G : Layers α) (infinite : (active G).Infinite) :
    (active (starLayers G)).Infinite := by
  apply (infinite.sdiff (Set.finite_singleton 0)).mono
  rintro i ⟨⟨word,member⟩,nonzero⟩
  have nonzero' : i≠0 := by simpa using nonzero
  have positive : 0 < i := by omega
  exact ⟨word,[i],[word],.cons ⟨positive,member⟩ .nil,by simp,by simp⟩

end IndexedSupport

namespace UniformGenerators.GlobalWordPolynomialTime

/-- Both the source index and its lucky accepting runtime can be bounded by
one polynomial in the produced word length. This is derived by truncating the
unary index, rather than by adding a per-layer fast-path requirement. -/
theorem bounded_witnesses {G : UniformGenerators α} (fast : G.GlobalWordPolynomialTime) :
    ∃ q : PolynomialBound,∀ word∈G.language,∃ i,i≤q word.length ∧ ∃ bits : BitString,
      bits≠[] ∧ G.machine.run (generatorData i) bits (q word.length)=.halted (.accepted word) := by
  obtain ⟨p,paths⟩ := fast.bounded_paths
  let q := globalWordIndexBound p
  have timeBound (m : ℕ) : p m≤q m := (Nat.le_succ _).trans (globalWordIndexBound_lower p m)
  refine ⟨q,fun word member=>?_⟩
  obtain ⟨i,index,bits,nonempty,run⟩ := paths word member
  refine ⟨i,index.trans (globalWordIndexBound_lower p word.length),bits,nonempty,?_⟩
  have padded := G.machine.run_halted_add (generatorData i) bits (p word.length) (.accepted word) run
    (q word.length-p word.length)
  rwa [Nat.add_sub_of_le (timeBound word.length)] at padded

end UniformGenerators.GlobalWordPolynomialTime

namespace OriginalSourceClosure

/-- A finite seed and positive source index; the runtime bound refers to the
length of the final concatenation, so it also bounds each individual factor. -/
def FastFactor (G : UniformGenerators α) (clock : ℕ) (request : ℕ × BitString) (word : List α) : Prop :=
  0 < request.1 ∧ request.2≠[] ∧
    G.machine.run (generatorData request.1) request.2 clock=.halted (.accepted word)

private theorem choose_factors (G : UniformGenerators α) (q : PolynomialBound)
    (paths : ∀ word∈G.language,∃ i,i≤q word.length ∧ ∃ bits : BitString,
      bits≠[] ∧ G.machine.run (generatorData i) bits (q word.length)=.halted (.accepted word))
    (zero : ∀ word∈G.layer 0,word=[])
    (m : ℕ) (words : List (List α))
    (members : ∀ word∈words,word∈G.language ∧ word≠[] ∧ word.length≤m) :
    ∃ requests : List (ℕ × BitString),
      List.Forall₂ (FastFactor G (q m)) requests words ∧
      (requests.map Prod.fst).sum≤words.length*q m := by
  induction words with
  | nil => exact ⟨[],.nil,by simp⟩
  | cons word words ih =>
      have head := members word (by simp)
      obtain ⟨i,index,bits,nonempty,run⟩ := paths word head.1
      have positive : 0 < i := by
        by_contra absent
        have equal : i=0 := by omega
        subst i
        exact head.2.1 (zero word ⟨bits,nonempty,q word.length,run⟩)
      have runtime : q word.length≤q m := q.monotone head.2.2
      have padded := G.machine.run_halted_add (generatorData i) bits (q word.length) (.accepted word) run
        (q m-q word.length)
      rw [Nat.add_sub_of_le runtime] at padded
      obtain ⟨requests,valid,bound⟩ := ih (fun u member => members u (by simp [member]))
      refine ⟨(i,bits)::requests,.cons ⟨positive,nonempty,padded⟩ valid,?_⟩
      simp only [List.map_cons,List.sum_cons,List.length_cons]
      have sourceIndex := index.trans runtime
      nlinarith

/-- A star word has at most one nonempty factor per output symbol. All its
source indices, source lucky runtimes and total producing index are bounded
by polynomials in the final word length, even when individual layers contain
arbitrarily long words. -/
theorem star_fast_factors (G : UniformGenerators α) (mean : G.ExpectedLength)
    (fast : G.GlobalWordPolynomialTime) :
    ∃ q : PolynomialBound,∀ word∈IndexedSupport.star G.language,
      ∃ requests : List (ℕ × BitString),∃ factors : List (List α),
        factors.flatten=word ∧ requests.length≤word.length ∧
        (requests.map Prod.fst).sum≤IndexedSupport.starBound q word.length ∧
        List.Forall₂ (FastFactor G (q word.length)) requests factors := by
  obtain ⟨q,paths⟩ := fast.bounded_witnesses
  refine ⟨q,?_⟩
  rintro word ⟨factors,members,rfl⟩
  obtain ⟨requests,valid,bound⟩ := choose_factors G q paths
    (fun _ member => G.word_eq_nil_of_expectedLength_zero mean member) factors.flatten.length factors
    (fun u belongs => ⟨(members u belongs).1,(members u belongs).2,
      IndexedSupport.factor_length_le factors u belongs⟩)
  have count := IndexedSupport.factors_count_le_length factors (fun u belongs => (members u belongs).2)
  refine ⟨requests,factors,rfl,?_,?_,valid⟩
  · exact valid.length_eq.le.trans count
  · exact bound.trans ((Nat.mul_le_mul_right _ count).trans (IndexedSupport.starBound_ge q factors.flatten.length))

end OriginalSourceClosure
end
end ComplexityOfGenerators
