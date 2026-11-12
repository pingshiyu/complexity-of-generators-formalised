import ComplexityOfGenerators.Foundations.FiniteBlockProbability

/-! Variable-width disjoint pieces of an actual fair finite bit block have
exactly the product law, including empty pieces and unused suffix padding. -/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

def splitBitVector (first second : ℕ) (bits : Fin (first + second) → Bool) :
    (Fin first → Bool) × (Fin second → Bool) :=
  (fun index => bits ⟨index.val, by omega⟩,
    fun index => bits ⟨first + index.val, by omega⟩)

def joinBitVector (first second : ℕ)
    (bits : (Fin first → Bool) × (Fin second → Bool)) : Fin (first + second) → Bool :=
  fun index => if left : index.val < first then bits.1 ⟨index.val, left⟩
    else bits.2 ⟨index.val - first, by have := index.isLt; omega⟩

def splitBitVectorEquiv (first second : ℕ) :
    (Fin (first + second) → Bool) ≃ (Fin first → Bool) × (Fin second → Bool) where
  toFun := splitBitVector first second
  invFun := joinBitVector first second
  left_inv bits := by
    funext index
    by_cases left : index.val < first
    · simp [joinBitVector, splitBitVector, left]
    · simp [joinBitVector, splitBitVector, left, Nat.add_sub_cancel' (by omega : first ≤ index.val)]
  right_inv bits := by
    apply Prod.ext
    · funext index
      simp [joinBitVector, splitBitVector, index.isLt]
    · funext index
      simp [joinBitVector, splitBitVector]

theorem fairBlockMeasure_map_splitBitVector (first second : ℕ) :
    (fairBlockMeasure (first + second)).map (splitBitVector first second) =
      (fairBlockMeasure first).prod (fairBlockMeasure second) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨left, right⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (left, right))]
  have preimage : (splitBitVector first second) ⁻¹' {(left, right)} =
      {(splitBitVectorEquiv first second).symm (left, right)} := by
    ext bits
    exact (splitBitVectorEquiv first second).eq_symm_apply.symm
  have singleton : {(left, right)} = {left} ×ˢ {right} := by simp
  rw [preimage, fairBlockMeasure_singleton, singleton, Measure.prod_prod,
    fairBlockMeasure_singleton, fairBlockMeasure_singleton, pow_add]

theorem ofFn_splitBitVector_left (first second : ℕ) (bits : Fin (first + second) → Bool) :
    List.ofFn (splitBitVector first second bits).1 = (List.ofFn bits).take first := by
  exact ofFn_takeBitVector (first + second) first (by omega) bits

theorem ofFn_splitBitVector_right (first second : ℕ) (bits : Fin (first + second) → Bool) :
    List.ofFn (splitBitVector first second bits).2 = (List.ofFn bits).drop first := by
  apply List.ext_getElem
  · simp
  · intro index left right
    simp [splitBitVector, List.getElem_ofFn, List.getElem_drop]

def splitThreeBitVectorEquiv (first second third : ℕ) :
    (Fin (first + (second + third)) → Bool) ≃
      (Fin first → Bool) × (Fin second → Bool) × (Fin third → Bool) :=
  (splitBitVectorEquiv first (second + third)).trans
    (Equiv.prodCongr (Equiv.refl _) (splitBitVectorEquiv second third))

theorem fairBlockMeasure_map_splitThreeBitVector (first second third : ℕ) :
    (fairBlockMeasure (first + (second + third))).map (splitThreeBitVectorEquiv first second third) =
      (fairBlockMeasure first).prod ((fairBlockMeasure second).prod (fairBlockMeasure third)) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨left, middle, right⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (left, middle, right))]
  have preimage : (splitThreeBitVectorEquiv first second third) ⁻¹' {(left, middle, right)} =
      {(splitThreeBitVectorEquiv first second third).symm (left, middle, right)} := by
    ext bits
    exact (splitThreeBitVectorEquiv first second third).eq_symm_apply.symm
  have singleton : {(left, middle, right)} = {left} ×ˢ ({middle} ×ˢ {right}) := by simp
  rw [preimage, fairBlockMeasure_singleton, singleton, Measure.prod_prod, Measure.prod_prod,
    fairBlockMeasure_singleton, fairBlockMeasure_singleton, fairBlockMeasure_singleton, pow_add, pow_add]

/-- Arbitrary suffix padding does not alter an initial block's law. -/
theorem fairBlockMeasure_map_takeBitVector (width count : ℕ) (fits : count ≤ width) :
    (fairBlockMeasure width).map (takeBitVector width count fits) = fairBlockMeasure count := by
  classical
  by_cases positive : 0 < count
  · apply Measure.ext
    intro event measurable
    rw [Measure.map_apply (measurable_of_countable _) measurable]
    exact fairBlockMeasure_prefix_event width count (by omega) positive fits event measurable
  · have zero : count = 0 := by omega
    subst count
    apply Measure.ext_of_singleton
    intro bits
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton bits)]
    have preimage : (takeBitVector width 0 fits) ⁻¹' {bits} = Set.univ := by
      ext source
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_univ, iff_true]
      funext index
      exact Fin.elim0 index
    rw [preimage, measure_univ, fairBlockMeasure_singleton]
    simp


def singleBitEquiv : (Fin 1 → Bool) ≃ Bool where
  toFun bits := bits 0
  invFun bit := fun _ => bit
  left_inv bits := by funext index; fin_cases index; rfl
  right_inv bit := rfl

/-- The native union layout places its fair-order bit after the two source
blocks. The product coordinates put that bit first for the mixture lemma. -/
def fairOfferBitEquiv (first second : ℕ) :
    (Fin (first + (second + 1)) → Bool) ≃ Bool × (Fin first → Bool) × (Fin second → Bool) :=
  (splitThreeBitVectorEquiv first second 1).trans
    ((Equiv.prodAssoc _ _ _).symm.trans
      ((Equiv.prodComm _ _).trans (Equiv.prodCongr singleBitEquiv (Equiv.refl _))))

theorem fairBlockMeasure_map_fairOfferBitEquiv (first second : ℕ) :
    (fairBlockMeasure (first + (second + 1))).map (fairOfferBitEquiv first second) =
      (PMF.uniformOfFintype Bool).toMeasure.prod
        ((fairBlockMeasure first).prod (fairBlockMeasure second)) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨coin, left, right⟩
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton (coin, left, right))]
  have preimage : (fairOfferBitEquiv first second) ⁻¹' {(coin, left, right)} =
      {(fairOfferBitEquiv first second).symm (coin, left, right)} := by
    ext bits
    exact (fairOfferBitEquiv first second).eq_symm_apply.symm
  have singleton : {(coin, left, right)} = {coin} ×ˢ ({left} ×ˢ {right}) := by simp
  rw [preimage, fairBlockMeasure_singleton, singleton, Measure.prod_prod, Measure.prod_prod,
    fairBlockMeasure_singleton, fairBlockMeasure_singleton]
  simp [PMF.uniformOfFintype_apply, pow_add, mul_comm, mul_left_comm, mul_assoc]

theorem fairOfferBitEquiv_left (first second : ℕ) (bits : Fin (first + (second + 1)) → Bool) :
    List.ofFn (fairOfferBitEquiv first second bits).2.1 = (List.ofFn bits).take first := by
  exact ofFn_splitBitVector_left first (second + 1) bits

theorem fairOfferBitEquiv_right (first second : ℕ) (bits : Fin (first + (second + 1)) → Bool) :
    List.ofFn (fairOfferBitEquiv first second bits).2.2 = ((List.ofFn bits).drop first).take second := by
  rw [← ofFn_splitBitVector_right first (second + 1) bits]
  exact ofFn_splitBitVector_left second 1 (splitBitVector first (second + 1) bits).2

theorem fairOfferBitEquiv_coin (first second : ℕ) (bits : Fin (first + (second + 1)) → Bool) :
    ((List.ofFn bits).drop (first + second)).head? = some (fairOfferBitEquiv first second bits).1 := by
  have indexBound : first + second < (List.ofFn bits).length := by
    simp only [List.length_ofFn]
    omega
  have lookup : ((List.ofFn bits).drop (first + second)).head? =
      some ((List.ofFn bits)[first + second]'indexBound) := by
    rw [List.head?_drop, List.getElem?_eq_getElem indexBound]
  rw [lookup]
  congr 1
  rw [List.getElem_ofFn]
  simp [fairOfferBitEquiv, splitThreeBitVectorEquiv, splitBitVectorEquiv,
    splitBitVector, singleBitEquiv]

end ComplexityOfGenerators
