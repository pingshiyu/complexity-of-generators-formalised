import ComplexityOfGenerators.Foundations.FiniteBlockPhases

/-! List-prefix semantics of the finite fair-block phase constructors. -/

namespace ComplexityOfGenerators.FiniteBlockPhase

open MeasureTheory

set_option backward.isDefEq.respectTransparency false

variable {α : Type}

def sample (bits : BitString) (width : ℕ) (enough : width ≤ bits.length) : Fin width → Bool :=
  fun index => bits[index.val]'(lt_of_lt_of_le index.isLt enough)

def evaluate (phase : FiniteBlockPhase α) (bits : BitString) : Option (List α) :=
  if enough : phase.width ≤ bits.length then phase.value (sample bits phase.width enough) else none

theorem evaluate_eq (phase : FiniteBlockPhase α) (bits : BitString) (enough : phase.width ≤ bits.length) :
    phase.evaluate bits = phase.value (sample bits phase.width enough) := by
  simp only [evaluate, dite_eq_left enough]

theorem evaluate_full (phase : FiniteBlockPhase α) (bits : Fin phase.width → Bool) :
    phase.evaluate (List.ofFn bits) = phase.value bits := by
  rw [evaluate_eq phase _ (by simp)]
  congr 1
  funext index
  simp [sample]

theorem ofFn_sample (bits : BitString) (width : ℕ) (enough : width ≤ bits.length) :
    List.ofFn (sample bits width enough) = bits.take width := by
  apply List.ext_getElem
  · simp [Nat.min_eq_left enough]
  · intro index left right
    simp [sample]


abbrev fromList (width : ℕ) (f : BitString → Option (List α)) : FiniteBlockPhase α :=
  ⟨width, fun bits => f (List.ofFn bits)⟩

theorem evaluate_fromList (width : ℕ) (f : BitString → Option (List α))
    (bits : BitString) (enough : width ≤ bits.length) :
    (fromList width f).evaluate bits = f (bits.take width) := by
  rw [evaluate_eq _ bits enough]
  change f (List.ofFn (sample bits width enough)) = _
  rw [ofFn_sample]

theorem evaluate_ofFn_prefix (phase : FiniteBlockPhase α) (width : ℕ) (fits : phase.width ≤ width)
    (bits : Fin width → Bool) :
    phase.evaluate (List.ofFn bits) = phase.value (takeBitVector width phase.width fits bits) := by
  rw [evaluate_eq _ _ (by simpa using fits)]
  congr 1
  funext index
  simp [sample, takeBitVector]

theorem evaluate_empty (bits : BitString) : (empty : FiniteBlockPhase α).evaluate bits = none := by
  rw [evaluate_eq _ bits (by simp)]

theorem evaluate_concatenate (first second : FiniteBlockPhase α) (bits : BitString)
    (enough : first.width + second.width ≤ bits.length) :
    (concatenate first second).evaluate bits =
      OptionPhase.append (first.evaluate bits) (second.evaluate (bits.drop first.width)) := by
  have firstEnough : first.width ≤ bits.length := by omega
  have secondEnough : second.width ≤ (bits.drop first.width).length := by simp; omega
  rw [evaluate_eq (concatenate first second) bits enough, evaluate_eq first bits firstEnough,
    evaluate_eq second _ secondEnough]
  have left : (splitBitVector first.width second.width (sample bits _ enough)).1 =
      sample bits first.width firstEnough := rfl
  have right : (splitBitVector first.width second.width (sample bits _ enough)).2 =
      sample (bits.drop first.width) second.width secondEnough := by
    funext index
    simp [sample, splitBitVector]
  change OptionPhase.append (first.value _) (second.value _) = _
  rw [left, right]

theorem evaluate_combine (first second : FiniteBlockPhase α) (bits : BitString)
    (enough : first.width + (second.width + 1) ≤ bits.length) :
    (combine first second).evaluate bits =
      OptionPhase.fairOffer ((bits.drop (first.width + second.width)).head? == some true)
        (first.evaluate bits) (second.evaluate (bits.drop first.width)) := by
  have firstEnough : first.width ≤ bits.length := by omega
  have secondEnough : second.width ≤ (bits.drop first.width).length := by simp; omega
  rw [evaluate_eq (combine first second) bits enough, evaluate_eq first bits firstEnough,
    evaluate_eq second _ secondEnough]
  let whole := sample bits (first.width + (second.width + 1)) enough
  have left : (fairOfferBitEquiv first.width second.width whole).2.1 =
      sample bits first.width firstEnough := rfl
  have right : (fairOfferBitEquiv first.width second.width whole).2.2 =
      sample (bits.drop first.width) second.width secondEnough := by
    funext index
    simp [whole, sample, fairOfferBitEquiv, splitThreeBitVectorEquiv, splitBitVectorEquiv, splitBitVector]
  have coin : ((bits.drop (first.width + second.width)).head? == some true) =
      (fairOfferBitEquiv first.width second.width whole).1 := by
    have inside : first.width + second.width < bits.length := by omega
    rw [List.head?_drop, List.getElem?_eq_getElem inside]
    change ((some (bits[first.width + second.width]'inside)) == some true) = bits[first.width + second.width]
    cases value : bits[first.width + second.width] <;> rfl
  change OptionPhase.fairOffer _ (first.value _) (second.value _) = _
  rw [left, right, coin]

theorem foldl_width_mono (phases : List (FiniteBlockPhase α)) (initial : FiniteBlockPhase α) :
    initial.width ≤ (phases.foldl combine initial).width := by
  induction phases generalizing initial with
  | nil => exact le_rfl
  | cons phase rest ih =>
    exact (show initial.width ≤ (combine initial phase).width by simp [combine]).trans (ih _)

def next (phase : FiniteBlockPhase α) (state : Option (List α) × BitString) : Option (List α) × BitString :=
  (OptionPhase.fairOffer ((state.2.drop phase.width).head? == some true) state.1 (phase.evaluate state.2),
    state.2.drop (phase.width + 1))

theorem next_prefix (initial phase : FiniteBlockPhase α) (bits : BitString)
    (enough : (combine initial phase).width ≤ bits.length) :
    next phase (initial.evaluate bits, bits.drop initial.width) =
      ((combine initial phase).evaluate bits, bits.drop (combine initial phase).width) := by
  rw [evaluate_combine initial phase bits enough]
  simp [next, combine, List.drop_drop, Nat.add_assoc]

/-- The left-fold phase uses exactly the same bounded tape pieces and offer
coins as a sequential scan of the corresponding optional outputs. -/
theorem foldl_evaluate (phases : List (FiniteBlockPhase α)) (initial : FiniteBlockPhase α)
    (bits : BitString) (enough : (phases.foldl combine initial).width ≤ bits.length) :
    phases.foldl (fun state phase => next phase state) (initial.evaluate bits, bits.drop initial.width) =
      ((phases.foldl combine initial).evaluate bits, bits.drop (phases.foldl combine initial).width) := by
  induction phases generalizing initial with
  | nil => rfl
  | cons phase rest ih =>
    rw [List.foldl_cons]
    rw [next_prefix initial phase bits ((foldl_width_mono rest _).trans enough)]
    exact ih (combine initial phase) enough


theorem evaluate_event_measure (phase : FiniteBlockPhase α) (width : ℕ) (fits : phase.width ≤ width)
    (event : Option (List α) → Prop) :
    fairBlockMeasure width {bits | event (phase.evaluate (List.ofFn bits))} =
      fairBlockMeasure phase.width {bits | event (phase.value bits)} := by
  simp_rw [evaluate_ofFn_prefix phase width fits]
  change fairBlockMeasure width ((takeBitVector width _ fits) ⁻¹' {bits | event (phase.value bits)}) = _
  rw [← Measure.map_apply (measurable_of_countable _) (Set.to_countable _ |>.measurableSet),
    fairBlockMeasure_map_takeBitVector]

theorem evaluate_mean (phase : FiniteBlockPhase α) (width target : ℕ) (fits : phase.width ≤ width)
    (balanced : phase.HasMean target) :
    OptionPhase.HasMean (fairBlockMeasure width) (fun bits => phase.evaluate (List.ofFn bits)) target := by
  have padded := OptionPhase.HasMean.padBitBlock width phase.width target fits phase.value balanced
  have values : (fun bits : Fin width → Bool => phase.evaluate (List.ofFn bits)) =
      fun bits => phase.value (takeBitVector width phase.width fits bits) := by
    funext bits
    exact evaluate_ofFn_prefix phase width fits bits
  rw [values]
  exact padded

end ComplexityOfGenerators.FiniteBlockPhase
