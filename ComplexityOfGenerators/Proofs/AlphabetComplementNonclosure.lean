import ComplexityOfGenerators.Proofs.AlphabetFallbackGeneration
import ComplexityOfGenerators.Proofs.NondeterministicUnion
import ComplexityOfGenerators.Proofs.ExpectedGenerationContainment
import ComplexityOfGenerators.Proofs.ExpectedLengthContainment
import ComplexityOfGenerators.Foundations.LanguageClosure

/-! Complement nonclosure over every nontrivial finite alphabet. The two
fallback generators use distinct alphabet letters, and all their native
sampling and verification costs are charged in AlphabetFallbackGeneration. -/
namespace ComplexityOfGenerators
noncomputable section
variable {α : Type} [Fintype α]

omit [Fintype α] in
theorem constantLetterLanguages_disjoint {a b : α} (different : a≠b) :
    constantLetterLanguage a∩constantLetterLanguage b=∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro word ⟨left,right⟩
  cases word with
  | nil => exact left.1 rfl
  | cons letter tail =>
      exact different ((left.2 letter (by simp)).symm.trans (right.2 letter (by simp)))

omit [Fintype α] in
theorem constantLetter_fallback_intersection (L : Language α) {a b : α} (different : a≠b) :
    (L∪constantLetterLanguage a)∩(L∪constantLetterLanguage b)=L := by
  ext word
  constructor
  · rintro ⟨left|left,right|right⟩
    · exact left
    · exact left
    · exact right
    · have impossible : word∈constantLetterLanguage a∩constantLetterLanguage b := ⟨left,right⟩
      rw [constantLetterLanguages_disjoint different] at impossible
      exact False.elim impossible
  · intro member;exact ⟨Or.inl member,Or.inl member⟩

omit [Fintype α] in
theorem union_constantLetterLanguage_infinite (L : Language α) (letter : α) :
    (L∪constantLetterLanguage letter).Infinite := by
  apply Set.infinite_of_injective_forall_mem (f:=fun n : ℕ=>List.replicate (n+1) letter)
  · intro n m equal
    have length := congrArg List.length equal
    simp only [List.length_replicate] at length
    omega
  · intro n
    apply Or.inr
    refine ⟨?_,?_⟩
    · intro empty
      have length := congrArg List.length empty
      simp at length
    · intro a member;exact (List.mem_replicate.mp member).2

/-- The obstruction only requires infinite polynomial generator languages
inside a class contained in NP; finite-language conventions play no role. -/
theorem not_complement_closed_of_infinite_pg_lift_alphabet [Nontrivial α]
    (C : LanguageClass α)
    (lift : ∀ {L : Language α},L.Infinite → L∈PG α → L∈C)
    (inside : C⊆NP α) (different : NP α≠coNP α) : ¬ClosedUnderComplement C := by
  obtain ⟨a,b,distinct⟩ := exists_pair_ne α
  intro closed
  apply different
  apply np_eq_coNP_iff_complement_closed.mpr
  intro L member
  have left := inside (closed _ (lift (union_constantLetterLanguage_infinite L a)
    (AlphabetFallbackGeneration.np_union_constantLetter_mem_pg member a)))
  have right := inside (closed _ (lift (union_constantLetterLanguage_infinite L b)
    (AlphabetFallbackGeneration.np_union_constantLetter_mem_pg member b)))
  have united := np_union left right
  have equal : (L∪constantLetterLanguage a)ᶜ∪(L∪constantLetterLanguage b)ᶜ=Lᶜ := by
    rw [←Set.compl_inter,constantLetter_fallback_intersection L distinct]
  exact equal ▸ united

theorem pg_not_complement_closed_alphabet [Nontrivial α] (different : NP α≠coNP α) :
    ¬ClosedUnderComplement (PG α) :=
  not_complement_closed_of_infinite_pg_lift_alphabet (PG α) (fun _ member=>member) pg_subset_np different

theorem epg_not_complement_closed_alphabet [Nontrivial α] (different : NP α≠coNP α) :
    ¬ClosedUnderComplement (EPG α) :=
  not_complement_closed_of_infinite_pg_lift_alphabet (EPG α) (fun _ member=>pg_subset_epg member) epg_subset_np different

theorem elepg_not_complement_closed_alphabet [Nontrivial α] (different : NP α≠coNP α) :
    ¬ClosedUnderComplement (ELEPG α) :=
  not_complement_closed_of_infinite_pg_lift_alphabet (ELEPG α)
    (fun infinite member=>pg_mem_elepg_of_infinite member infinite) elepg_subset_np different

end
end ComplexityOfGenerators
