import ComplexityOfGenerators.Foundations.FixedBlockRetries
import ComplexityOfGenerators.Foundations.FixedBitBlocks

/-! Uniform finite-bit counting for the shared executable block codec. -/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

theorem fairBlockMeasure_singleton (width : ℕ) (bits : Fin width → Bool) :
    fairBlockMeasure width {bits} = (2 : ℝ≥0∞)⁻¹ ^ width := by
  rw [fairBlockMeasure, Measure.infinitePi_singleton_of_fintype]
  simp [PMF.uniformOfFintype_apply]

theorem fairBlockMeasure_eq_uniform (width : ℕ) :
    fairBlockMeasure width = (PMF.uniformOfFintype (Fin width → Bool)).toMeasure := by
  apply Measure.ext_of_singleton
  intro bits
  rw [fairBlockMeasure_singleton]
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

def blockListEquiv (width : ℕ) : (Fin width → Bool) ≃ {bits : BitString // bits.length = width} where
  toFun bits := ⟨List.ofFn bits, by simp⟩
  invFun bits := fun index => bits.val[index.val]'(by simpa [bits.property] using index.isLt)
  left_inv bits := by funext index; simp
  right_inv bits := by
    apply Subtype.ext
    simpa [bits.property] using (List.ofFn_getElem (xs := bits.val))

def bitVectorEquiv (width : ℕ) : (Fin width → Bool) ≃ Fin (2 ^ width) :=
  (blockListEquiv width).trans (FixedBitBlocks.blockEquiv width)

@[simp] theorem bitVectorEquiv_value (width : ℕ) (bits : Fin width → Bool) :
    (bitVectorEquiv width bits).val = FixedBitBlocks.decode (List.ofFn bits) := rfl

theorem fairBlockMeasure_map_bitVectorEquiv (width : ℕ) :
    (fairBlockMeasure width).map (bitVectorEquiv width) =
      (PMF.uniformOfFintype (Fin (2 ^ width))).toMeasure := by
  apply Measure.ext_of_singleton
  intro value
  rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton value)]
  have preimage : (bitVectorEquiv width) ⁻¹' {value} = {(bitVectorEquiv width).symm value} := by
    ext bits
    exact (bitVectorEquiv width).eq_symm_apply.symm
  rw [preimage, fairBlockMeasure_singleton]
  simp [PMF.uniformOfFintype_apply, ENNReal.inv_pow]

def finBelowEquiv (size bound : ℕ) (fits : bound ≤ size) :
    {value : Fin size // value.val < bound} ≃ Fin bound where
  toFun value := ⟨value.val.val, value.property⟩
  invFun value := ⟨⟨value.val, lt_of_lt_of_le value.isLt fits⟩, value.isLt⟩
  left_inv value := by apply Subtype.ext; apply Fin.ext; rfl
  right_inv value := by apply Fin.ext; rfl

def finIntervalEquiv (size lower upper : ℕ) (ordered : lower ≤ upper) (fits : upper ≤ size) :
    {value : Fin size // lower ≤ value.val ∧ value.val < upper} ≃ Fin (upper - lower) where
  toFun value := ⟨value.val.val - lower, by have := value.property; omega⟩
  invFun value := ⟨⟨lower + value.val, by have := value.isLt; omega⟩,
    by change lower ≤ lower + value.val ∧ lower + value.val < upper; have := value.isLt; omega⟩
  left_inv value := by apply Subtype.ext; apply Fin.ext; simp; have := value.property; omega
  right_inv value := by apply Fin.ext; simp

theorem uniformFin_below (size bound : ℕ) [NeZero size] (fits : bound ≤ size) :
    (PMF.uniformOfFintype (Fin size)).toMeasure {value | value.val < bound} =
      (bound : ℝ≥0∞) / size := by
  classical
  rw [PMF.toMeasure_uniformOfFintype_apply (α := Fin size) (s := {value | value.val < bound})
    (by exact Set.to_countable _ |>.measurableSet)]
  have card : Fintype.card ↥({value : Fin size | value.val < bound}) = bound :=
    (Fintype.card_congr (finBelowEquiv size bound fits)).trans (Fintype.card_fin bound)
  rw [card]
  simp

theorem uniformFin_interval (size lower upper : ℕ) [NeZero size]
    (ordered : lower ≤ upper) (fits : upper ≤ size) :
    (PMF.uniformOfFintype (Fin size)).toMeasure {value | lower ≤ value.val ∧ value.val < upper} =
      ((upper - lower : ℕ) : ℝ≥0∞) / size := by
  classical
  rw [PMF.toMeasure_uniformOfFintype_apply (α := Fin size) (s := {value | lower ≤ value.val ∧ value.val < upper})
    (by exact Set.to_countable _ |>.measurableSet)]
  have card : Fintype.card ↥({value : Fin size | lower ≤ value.val ∧ value.val < upper}) = upper - lower :=
    (Fintype.card_congr (finIntervalEquiv size lower upper ordered fits)).trans (Fintype.card_fin _)
  rw [card]
  simp

theorem fairBlockMeasure_decode_below (width bound : ℕ) (fits : bound ≤ 2 ^ width) :
    fairBlockMeasure width {bits | FixedBitBlocks.decode (List.ofFn bits) < bound} =
      (bound : ℝ≥0∞) / ((2 ^ width : ℕ) : ℝ≥0∞) := by
  have event : {bits | FixedBitBlocks.decode (List.ofFn bits) < bound} =
      (bitVectorEquiv width) ⁻¹' {value | value.val < bound} := rfl
  rw [event, ← Measure.map_apply (measurable_of_countable _)
    (by exact Set.to_countable _ |>.measurableSet), fairBlockMeasure_map_bitVectorEquiv]
  exact uniformFin_below (2 ^ width) bound fits

theorem fairBlockMeasure_decode_interval (width lower upper : ℕ)
    (ordered : lower ≤ upper) (fits : upper ≤ 2 ^ width) :
    fairBlockMeasure width {bits | lower ≤ FixedBitBlocks.decode (List.ofFn bits) ∧
      FixedBitBlocks.decode (List.ofFn bits) < upper} =
      ((upper - lower : ℕ) : ℝ≥0∞) / ((2 ^ width : ℕ) : ℝ≥0∞) := by
  have event : {bits | lower ≤ FixedBitBlocks.decode (List.ofFn bits) ∧ FixedBitBlocks.decode (List.ofFn bits) < upper} =
      (bitVectorEquiv width) ⁻¹' {value | lower ≤ value.val ∧ value.val < upper} := rfl
  rw [event, ← Measure.map_apply (measurable_of_countable _)
    (by exact Set.to_countable _ |>.measurableSet), fairBlockMeasure_map_bitVectorEquiv]
  exact uniformFin_interval (2 ^ width) lower upper ordered fits

def takeBitVector (width count : ℕ) (fits : count ≤ width) (bits : Fin width → Bool) : Fin count → Bool :=
  fun index => bits ⟨index.val, lt_of_lt_of_le index.isLt fits⟩

theorem ofFn_takeBitVector (width count : ℕ) (fits : count ≤ width) (bits : Fin width → Bool) :
    List.ofFn (takeBitVector width count fits bits) = (List.ofFn bits).take count := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left fits]
  · intro j left right
    simp [takeBitVector, List.getElem_ofFn, List.getElem_take]

/-- Any initial subblock of a uniform finite block is itself uniform. -/
theorem fairBlockMeasure_prefix_event (width count : ℕ) (widthPositive : 0 < width)
    (countPositive : 0 < count) (fits : count ≤ width)
    (event : Set (Fin count → Bool)) (measurable : MeasurableSet event) :
    fairBlockMeasure width {bits | takeBitVector width count fits bits ∈ event} = fairBlockMeasure count event := by
  classical
  rw [← fairCoinMeasure_fixedBlock_event width widthPositive 0 _ (by exact Set.to_countable _ |>.measurableSet)]
  have equal : {stream | takeBitVector width count fits (fixedBlock width stream 0) ∈ event} =
      {stream | fixedBlock count stream 0 ∈ event} := by
    ext stream
    have values : takeBitVector width count fits (fixedBlock width stream 0) = fixedBlock count stream 0 := by
      funext index
      simp [takeBitVector, fixedBlock]
    change takeBitVector width count fits (fixedBlock width stream 0) ∈ event ↔ _
    rw [values]
    rfl
  change fairCoinMeasure {stream | takeBitVector width count fits (fixedBlock width stream 0) ∈ event} = _
  rw [equal, fairCoinMeasure_fixedBlock_event count countPositive 0 event measurable]


def fixedBlockTriple (width : ℕ) (stream : BitStream) :
    (Fin width → Bool) × (Fin width → Bool) × (Fin width → Bool) :=
  (fixedBlock width stream 0, fixedBlock width stream 1, fixedBlock width stream 2)

theorem fairCoinMeasure_map_fixedBlockTriple (width : ℕ) (positive : 0 < width) :
    fairCoinMeasure.map (fixedBlockTriple width) =
      (fairBlockMeasure width).prod ((fairBlockMeasure width).prod (fairBlockMeasure width)) := by
  classical
  apply Measure.ext_of_singleton
  rintro ⟨first, second, third⟩
  have measurable : Measurable (fixedBlockTriple width) :=
    ((measurable_fixedBlocks width).eval (a := 0)).prodMk
      (((measurable_fixedBlocks width).eval (a := 1)).prodMk
        ((measurable_fixedBlocks width).eval (a := 2)))
  rw [Measure.map_apply measurable
    (measurableSet_singleton (first, second, third))]
  let events : ℕ → Set (Fin width → Bool) :=
    fun phase => if phase = 0 then {first} else if phase = 1 then {second} else {third}
  have equal : (fixedBlockTriple width) ⁻¹' {(first, second, third)} =
      {stream | ∀ phase ∈ Finset.range 3, fixedBlock width stream phase ∈ events phase} := by
    ext stream
    change fixedBlockTriple width stream = (first, second, third) ↔ _
    constructor
    · intro same phase member
      have small : phase < 3 := Finset.mem_range.mp member
      interval_cases phase <;> simp_all [fixedBlockTriple, events, Prod.mk.injEq]
    · intro member
      have zero := member 0 (by simp)
      have one := member 1 (by simp)
      have two := member 2 (by simp)
      simpa [events, fixedBlockTriple, Prod.mk.injEq] using And.intro zero (And.intro one two)
  rw [equal, fairCoinMeasure_fixedBlock_events width positive _ events
    (fun _ => Set.to_countable _ |>.measurableSet)]
  have singleton : {(first, second, third)} = {first} ×ˢ ({second} ×ˢ {third}) := by simp
  rw [singleton, Measure.prod_prod, Measure.prod_prod]
  simp [Finset.prod_range_succ, events, mul_assoc]

end ComplexityOfGenerators
