import ComplexityOfGenerators.Foundations.FiniteBlockPhaseLists
import ComplexityOfGenerators.Proofs.PolynomialUnionSupport

/-! Exact means and full support of the existing bounded native union value. -/

namespace ComplexityOfGenerators.Simulation.UnionGenerator

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

abbrev sourcePhase (M : Machine Unit Bool α) (seed time : PolynomialBound) (n : ℕ) : FiniteBlockPhase α :=
  FiniteBlockPhase.fromList (seed n) (sourceValue M time n)

abbrev offerPhase (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) : FiniteBlockPhase α :=
  FiniteBlockPhase.combine (sourcePhase G leftSeed leftTime n) (sourcePhase H rightSeed rightTime n)

theorem value_eq_offerPhase (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ)
    (bits : BitString) (enough : (offerPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ bits.length) :
    value G H leftSeed leftTime rightSeed rightTime n bits =
      (offerPhase G H leftSeed leftTime rightSeed rightTime n).evaluate bits := by
  rw [FiniteBlockPhase.evaluate_combine _ _ bits enough]
  rw [FiniteBlockPhase.evaluate_fromList _ _ bits (by change leftSeed n + (rightSeed n + 1) ≤ bits.length at enough; omega),
    FiniteBlockPhase.evaluate_fromList _ _ (bits.drop (leftSeed n)) (by
      simp only [List.length_drop]
      change leftSeed n + (rightSeed n + 1) ≤ bits.length at enough
      omega)]
  simp only [value, OptionPhase.fairOffer, OptionPhase.offer_eq_or, beq_iff_eq]

theorem offerPhase_width_le (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) :
    (offerPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ unionSeed leftSeed rightSeed n := by
  have lower := unionSeed_lower leftSeed rightSeed n
  change leftSeed n + (rightSeed n + 1) ≤ _
  omega

theorem value_mean (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (offerPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width)
    (left : (sourcePhase G leftSeed leftTime n).HasMean n)
    (right : (sourcePhase H rightSeed rightTime n).HasMean n) :
    OptionPhase.HasMean (fairBlockMeasure width)
      (fun bits => value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)) n := by
  have balanced := FiniteBlockPhase.combine_mean (sourcePhase G leftSeed leftTime n)
    (sourcePhase H rightSeed rightTime n) n left right
  have values : ∀ bits : Fin width → Bool, value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits) =
      (offerPhase G H leftSeed leftTime rightSeed rightTime n).evaluate (List.ofFn bits) := by
    intro bits
    exact value_eq_offerPhase G H leftSeed leftTime rightSeed rightTime n _ (by simpa using fits)
  simpa only [values] using FiniteBlockPhase.evaluate_mean
    (offerPhase G H leftSeed leftTime rightSeed rightTime n) width n fits balanced

theorem value_mean_full_seed (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ)
    (left : (sourcePhase G leftSeed leftTime n).HasMean n)
    (right : (sourcePhase H rightSeed rightTime n).HasMean n) :
    OptionPhase.HasMean (fairBlockMeasure (unionSeed leftSeed rightSeed n))
      (fun bits => value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)) n :=
  value_mean G H leftSeed leftTime rightSeed rightTime n _
    (offerPhase_width_le G H leftSeed leftTime rightSeed rightTime n) left right

theorem value_event_measure (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (offerPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width)
    (event : Option (List α) → Prop) :
    fairBlockMeasure width {bits | event (value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits))} =
      fairBlockMeasure (offerPhase G H leftSeed leftTime rightSeed rightTime n).width
        {bits | event ((offerPhase G H leftSeed leftTime rightSeed rightTime n).value bits)} := by
  have values : ∀ bits : Fin width → Bool, value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits) =
      (offerPhase G H leftSeed leftTime rightSeed rightTime n).evaluate (List.ofFn bits) := by
    intro bits
    exact value_eq_offerPhase G H leftSeed leftTime rightSeed rightTime n _ (by simpa using fits)
  simpa only [values] using FiniteBlockPhase.evaluate_event_measure
    (offerPhase G H leftSeed leftTime rightSeed rightTime n) width fits event

theorem value_word_probability (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (offerPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width) (word : List α) :
    (0 < fairBlockMeasure width {bits |
      value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits) = some word}) ↔
      word ∈ (sourcePhase G leftSeed leftTime n).language ∨ word ∈ (sourcePhase H rightSeed rightTime n).language := by
  rw [value_event_measure G H leftSeed leftTime rightSeed rightTime n width fits (fun answer => answer = some word)]
  exact FiniteBlockPhase.combine_language _ _ word


theorem value_success_ge_left (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (offerPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width) :
    (sourcePhase G leftSeed leftTime n).successMass ≤ fairBlockMeasure width {bits |
      (value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)).isSome} := by
  rw [value_event_measure G H leftSeed leftTime rightSeed rightTime n width fits (fun answer => answer.isSome = true)]
  exact FiniteBlockPhase.combine_success_ge_left _ _

theorem value_success_ge_right (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (offerPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width) :
    (sourcePhase H rightSeed rightTime n).successMass ≤ fairBlockMeasure width {bits |
      (value G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)).isSome} := by
  rw [value_event_measure G H leftSeed leftTime rightSeed rightTime n width fits (fun answer => answer.isSome = true)]
  exact FiniteBlockPhase.combine_success_ge_right _ _

end ComplexityOfGenerators.Simulation.UnionGenerator
