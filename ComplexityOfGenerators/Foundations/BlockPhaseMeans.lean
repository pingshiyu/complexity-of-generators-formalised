import ComplexityOfGenerators.Foundations.OptionPhaseMeans
import ComplexityOfGenerators.Foundations.VariableBitBlocks

/-! The option-phase first moments instantiated on concrete independent
pieces of one fair finite random tape. -/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

namespace OptionPhase

variable {α : Type}

theorem HasMean.bitAppend (firstWidth secondWidth firstTarget secondTarget : ℕ)
    (first : (Fin firstWidth → Bool) → Option (List α))
    (second : (Fin secondWidth → Bool) → Option (List α))
    (leftMean : HasMean (fairBlockMeasure firstWidth) first firstTarget)
    (rightMean : HasMean (fairBlockMeasure secondWidth) second secondTarget) :
    HasMean (fairBlockMeasure (firstWidth + secondWidth))
      (fun bits => OptionPhase.append (first (splitBitVector firstWidth secondWidth bits).1)
        (second (splitBitVector firstWidth secondWidth bits).2)) (firstTarget + secondTarget) := by
  exact HasMean.pullback _ _ _ (fairBlockMeasure_map_splitBitVector firstWidth secondWidth) _ _
    (HasMean.append _ _ first second firstTarget secondTarget leftMean rightMean)

theorem HasMean.bitFairOffer (firstWidth secondWidth target : ℕ)
    (first : (Fin firstWidth → Bool) → Option (List α))
    (second : (Fin secondWidth → Bool) → Option (List α))
    (leftMean : HasMean (fairBlockMeasure firstWidth) first target)
    (rightMean : HasMean (fairBlockMeasure secondWidth) second target) :
    HasMean (fairBlockMeasure (firstWidth + (secondWidth + 1)))
      (fun bits => OptionPhase.fairOffer (fairOfferBitEquiv firstWidth secondWidth bits).1
        (first (fairOfferBitEquiv firstWidth secondWidth bits).2.1)
        (second (fairOfferBitEquiv firstWidth secondWidth bits).2.2)) target := by
  exact HasMean.pullback _ _ _ (fairBlockMeasure_map_fairOfferBitEquiv firstWidth secondWidth) _ _
    (HasMean.fairOffer _ _ first second target leftMean rightMean)

theorem HasMean.padBitBlock (width count target : ℕ) (fits : count ≤ width)
    (phase : (Fin count → Bool) → Option (List α))
    (balanced : HasMean (fairBlockMeasure count) phase target) :
    HasMean (fairBlockMeasure width) (fun bits => phase (takeBitVector width count fits bits)) target :=
  HasMean.pullback _ _ _ (fairBlockMeasure_map_takeBitVector width count fits) phase target balanced

end OptionPhase

/-- Every particular finite fair bit block has positive mass, including the
unique block of length zero. -/
theorem fairBlockMeasure_event_pos_iff (width : ℕ) (event : Set (Fin width → Bool)) :
    0 < fairBlockMeasure width event ↔ event.Nonempty := by
  constructor
  · exact fun positive => nonempty_of_measure_ne_zero positive.ne'
  · rintro ⟨bits, member⟩
    have positive : 0 < fairBlockMeasure width {bits} := by
      rw [fairBlockMeasure_singleton]
      exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0))
    exact positive.trans_le (measure_mono (Set.singleton_subset_iff.mpr member))


namespace OptionPhase

variable {α : Type}

theorem offer_returns_input (first second : Option (List α)) (word : List α)
    (accepted : offer first second = some word) : first = some word ∨ second = some word := by
  cases first with
  | none => exact Or.inr accepted
  | some left => exact Or.inl accepted

theorem fairOffer_returns_input (coin : Bool) (first second : Option (List α)) (word : List α)
    (accepted : fairOffer coin first second = some word) : first = some word ∨ second = some word := by
  cases coin with
  | false => exact offer_returns_input first second word accepted
  | true => exact (offer_returns_input second first word accepted).symm

/-- A fair-order offer preserves the complete positive-probability support
of both input blocks, even if either input always succeeds. -/
theorem bitFairOffer_word_probability (firstWidth secondWidth : ℕ)
    (first : (Fin firstWidth → Bool) → Option (List α))
    (second : (Fin secondWidth → Bool) → Option (List α)) (word : List α) :
    (0 < fairBlockMeasure (firstWidth + (secondWidth + 1)) {bits |
      fairOffer (fairOfferBitEquiv firstWidth secondWidth bits).1
        (first (fairOfferBitEquiv firstWidth secondWidth bits).2.1)
        (second (fairOfferBitEquiv firstWidth secondWidth bits).2.2) = some word}) ↔
      (0 < fairBlockMeasure firstWidth {bits | first bits = some word}) ∨
        (0 < fairBlockMeasure secondWidth {bits | second bits = some word}) := by
  simp only [fairBlockMeasure_event_pos_iff, Set.Nonempty, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨bits, accepted⟩
    rcases fairOffer_returns_input _ _ _ word accepted with left | right
    · exact Or.inl ⟨_, left⟩
    · exact Or.inr ⟨_, right⟩
  · rintro (⟨left, accepted⟩ | ⟨right, accepted⟩)
    · let parts : Bool × (Fin firstWidth → Bool) × (Fin secondWidth → Bool) := (false, left, fun _ => false)
      refine ⟨(fairOfferBitEquiv firstWidth secondWidth).symm parts, ?_⟩
      rw [(fairOfferBitEquiv firstWidth secondWidth).apply_symm_apply]
      simp [parts, fairOffer, offer, accepted]
    · let parts : Bool × (Fin firstWidth → Bool) × (Fin secondWidth → Bool) := (true, (fun _ => false), right)
      refine ⟨(fairOfferBitEquiv firstWidth secondWidth).symm parts, ?_⟩
      rw [(fairOfferBitEquiv firstWidth secondWidth).apply_symm_apply]
      simp [parts, fairOffer, offer, accepted]

/-- Independent concatenation has exactly the product language support. -/
theorem bitAppend_word_probability (firstWidth secondWidth : ℕ)
    (first : (Fin firstWidth → Bool) → Option (List α))
    (second : (Fin secondWidth → Bool) → Option (List α)) (word : List α) :
    (0 < fairBlockMeasure (firstWidth + secondWidth) {bits |
      OptionPhase.append (first (splitBitVector firstWidth secondWidth bits).1)
        (second (splitBitVector firstWidth secondWidth bits).2) = some word}) ↔
      ∃ left right, (0 < fairBlockMeasure firstWidth {bits | first bits = some left}) ∧
        (0 < fairBlockMeasure secondWidth {bits | second bits = some right}) ∧ left ++ right = word := by
  simp only [fairBlockMeasure_event_pos_iff, Set.Nonempty, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨bits, accepted⟩
    cases left : first (splitBitVector firstWidth secondWidth bits).1 with
    | none => simp [append, left] at accepted
    | some firstWord =>
      cases right : second (splitBitVector firstWidth secondWidth bits).2 with
      | none => simp [append, left, right] at accepted
      | some secondWord =>
        exact ⟨firstWord, secondWord, ⟨_, left⟩, ⟨_, right⟩, by simpa [append, left, right] using accepted⟩
  · rintro ⟨left, right, ⟨leftBits, leftRun⟩, ⟨rightBits, rightRun⟩, wordEq⟩
    refine ⟨(splitBitVectorEquiv firstWidth secondWidth).symm (leftBits, rightBits), ?_⟩
    have split : splitBitVector firstWidth secondWidth
        ((splitBitVectorEquiv firstWidth secondWidth).symm (leftBits, rightBits)) = (leftBits, rightBits) :=
      (splitBitVectorEquiv firstWidth secondWidth).apply_symm_apply _
    rw [split]
    simp [append, leftRun, rightRun, wordEq]

end OptionPhase


namespace OptionPhase

variable {α : Type}

theorem bitFairOffer_success_ge_left (firstWidth secondWidth : ℕ)
    (first : (Fin firstWidth → Bool) → Option (List α))
    (second : (Fin secondWidth → Bool) → Option (List α)) :
    fairBlockMeasure firstWidth (success first) ≤
      fairBlockMeasure (firstWidth + (secondWidth + 1)) (success (fun bits =>
        fairOffer (fairOfferBitEquiv firstWidth secondWidth bits).1
          (first (fairOfferBitEquiv firstWidth secondWidth bits).2.1)
          (second (fairOfferBitEquiv firstWidth secondWidth bits).2.2))) := by
  have lower := fairOffer_success_ge_left (fairBlockMeasure firstWidth) (fairBlockMeasure secondWidth) first second
  rw [← fairBlockMeasure_map_fairOfferBitEquiv,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _ |>.measurableSet)] at lower
  exact lower

theorem bitFairOffer_success_ge_right (firstWidth secondWidth : ℕ)
    (first : (Fin firstWidth → Bool) → Option (List α))
    (second : (Fin secondWidth → Bool) → Option (List α)) :
    fairBlockMeasure secondWidth (success second) ≤
      fairBlockMeasure (firstWidth + (secondWidth + 1)) (success (fun bits =>
        fairOffer (fairOfferBitEquiv firstWidth secondWidth bits).1
          (first (fairOfferBitEquiv firstWidth secondWidth bits).2.1)
          (second (fairOfferBitEquiv firstWidth secondWidth bits).2.2))) := by
  have lower := fairOffer_success_ge_right (fairBlockMeasure firstWidth) (fairBlockMeasure secondWidth) first second
  rw [← fairBlockMeasure_map_fairOfferBitEquiv,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _ |>.measurableSet)] at lower
  exact lower

end OptionPhase

end ComplexityOfGenerators
