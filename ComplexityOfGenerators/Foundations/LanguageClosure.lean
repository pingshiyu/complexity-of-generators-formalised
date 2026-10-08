import ComplexityOfGenerators.ComplexityClasses

/-! Extensional language closure and the complement duality used in 7.2. -/

namespace ComplexityOfGenerators

/-- Closed under complement relative to the full universe of words. -/
def ClosedUnderComplement {α : Type} (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → Lᶜ ∈ C

/-- Closed under binary language intersection. -/
def ClosedUnderIntersection {α : Type} (C : LanguageClass α) : Prop :=
  ∀ L K, L ∈ C → K ∈ C → L ∩ K ∈ C

theorem np_eq_coNP_iff_complement_closed {α : Type} [Fintype α] :
    NP α = coNP α ↔ ClosedUnderComplement (NP α) := by
  constructor
  · intro equal L member
    have : L ∈ coNP α := equal ▸ member
    exact this
  · intro closed
    apply Set.Subset.antisymm
    · intro L member
      exact closed L member
    · intro L member
      have complement : Lᶜ ∈ NP α := member
      simpa using closed Lᶜ complement

/-- Native NP/coNP duality, without a comparison to another machine model. -/
theorem np_ne_coNP_witness {α : Type} [Fintype α] (different : NP α ≠ coNP α) :
    ∃ L : Language α, L ∈ NP α ∧ Lᶜ ∉ NP α := by
  classical
  by_contra absent
  apply different
  apply np_eq_coNP_iff_complement_closed.mpr
  intro L member
  by_contra outside
  exact absent ⟨L, member, outside⟩

/-- Positive constant-bit words. The empty word belongs to neither filler
language, so their supports are disjoint also at the length-zero boundary. -/
def constantBitLanguage (bit : Bool) : Language Bool :=
  {w | w ≠ [] ∧ ∀ letter ∈ w, letter = bit}

theorem constantBitLanguages_disjoint :
    constantBitLanguage false ∩ constantBitLanguage true = ∅ := by
  apply Set.eq_empty_iff_forall_notMem.mpr
  rintro word ⟨left, right⟩
  cases word with
  | nil => exact left.1 rfl
  | cons bit tail =>
      have zero := left.2 bit (by simp)
      have one := right.2 bit (by simp)
      exact Bool.false_ne_true (zero.symm.trans one)

/-- Two distinct fallbacks cancel in an intersection. Using constant-bit words
avoids an additional prefix-removal compiler in the collision-language proof. -/
theorem fallback_intersection (L : Language Bool) :
    (L ∪ constantBitLanguage false) ∩ (L ∪ constantBitLanguage true) = L := by
  ext word
  constructor
  · rintro ⟨left | zero, right | one⟩
    · exact left
    · exact left
    · exact right
    · have impossible : word ∈ constantBitLanguage false ∩ constantBitLanguage true := ⟨zero, one⟩
      rw [constantBitLanguages_disjoint] at impossible
      exact False.elim impossible
  · intro member
    exact ⟨Or.inl member, Or.inl member⟩

end ComplexityOfGenerators
