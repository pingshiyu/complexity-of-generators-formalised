import ComplexityOfGenerators.Foundations.BlockPhaseMeans

/-! Concrete finite phases closed under independent concatenation and fair
flag-only offers. The scan is the finite policy used by native concatenation. -/

namespace ComplexityOfGenerators

set_option backward.isDefEq.respectTransparency false

open MeasureTheory
open scoped ENNReal

structure FiniteBlockPhase (α : Type) where
  width : ℕ
  value : (Fin width → Bool) → Option (List α)

namespace FiniteBlockPhase

variable {α : Type}

def HasMean (phase : FiniteBlockPhase α) (target : ℕ) : Prop :=
  OptionPhase.HasMean (fairBlockMeasure phase.width) phase.value target

def language (phase : FiniteBlockPhase α) : Language α :=
  {word | 0 < fairBlockMeasure phase.width {bits | phase.value bits = some word}}

abbrev empty : FiniteBlockPhase α := ⟨0, fun _ => none⟩

abbrev concatenate (first second : FiniteBlockPhase α) : FiniteBlockPhase α :=
  ⟨first.width + second.width, fun bits =>
    OptionPhase.append (first.value (splitBitVector first.width second.width bits).1)
      (second.value (splitBitVector first.width second.width bits).2)⟩

abbrev combine (first second : FiniteBlockPhase α) : FiniteBlockPhase α :=
  ⟨first.width + (second.width + 1), fun bits =>
    OptionPhase.fairOffer (fairOfferBitEquiv first.width second.width bits).1
      (first.value (fairOfferBitEquiv first.width second.width bits).2.1)
      (second.value (fairOfferBitEquiv first.width second.width bits).2.2)⟩

def scan (phases : List (FiniteBlockPhase α)) : FiniteBlockPhase α := phases.foldl combine empty

theorem empty_mean (target : ℕ) : (empty : FiniteBlockPhase α).HasMean target := by
  simp [HasMean, empty, OptionPhase.HasMean, OptionPhase.success, BalancedPairPhase.optionLength]

theorem concatenate_mean (first second : FiniteBlockPhase α) (firstTarget secondTarget : ℕ)
    (left : first.HasMean firstTarget) (right : second.HasMean secondTarget) :
    (concatenate first second).HasMean (firstTarget + secondTarget) :=
  OptionPhase.HasMean.bitAppend first.width second.width firstTarget secondTarget first.value second.value left right

theorem combine_mean (first second : FiniteBlockPhase α) (target : ℕ)
    (left : first.HasMean target) (right : second.HasMean target) :
    (combine first second).HasMean target :=
  OptionPhase.HasMean.bitFairOffer first.width second.width target first.value second.value left right

theorem combine_language (first second : FiniteBlockPhase α) (word : List α) :
    word ∈ (combine first second).language ↔ word ∈ first.language ∨ word ∈ second.language :=
  OptionPhase.bitFairOffer_word_probability first.width second.width first.value second.value word

theorem concatenate_language (first second : FiniteBlockPhase α) (word : List α) :
    word ∈ (concatenate first second).language ↔
      ∃ left right, left ∈ first.language ∧ right ∈ second.language ∧ left ++ right = word :=
  OptionPhase.bitAppend_word_probability first.width second.width first.value second.value word

@[simp] theorem empty_language : (empty : FiniteBlockPhase α).language = ∅ := by
  ext word
  simp [language, empty]

theorem foldl_mean (phases : List (FiniteBlockPhase α)) (initial : FiniteBlockPhase α) (target : ℕ)
    (start : initial.HasMean target) (balanced : ∀ phase ∈ phases, phase.HasMean target) :
    (phases.foldl combine initial).HasMean target := by
  induction phases generalizing initial with
  | nil => exact start
  | cons phase rest ih =>
    exact ih (combine initial phase) (combine_mean initial phase target start (balanced phase (by simp)))
      (fun p member => balanced p (by simp [member]))

theorem scan_mean (phases : List (FiniteBlockPhase α)) (target : ℕ)
    (balanced : ∀ phase ∈ phases, phase.HasMean target) : (scan phases).HasMean target :=
  foldl_mean phases empty target (empty_mean target) balanced

theorem foldl_language (phases : List (FiniteBlockPhase α)) (initial : FiniteBlockPhase α) (word : List α) :
    word ∈ (phases.foldl combine initial).language ↔
      word ∈ initial.language ∨ ∃ phase ∈ phases, word ∈ phase.language := by
  induction phases generalizing initial with
  | nil => simp
  | cons phase rest ih =>
    rw [List.foldl_cons, ih, combine_language]
    simp only [List.mem_cons]
    constructor
    · rintro ((old | current) | ⟨p, member, supported⟩)
      · exact Or.inl old
      · exact Or.inr ⟨phase, Or.inl rfl, current⟩
      · exact Or.inr ⟨p, Or.inr member, supported⟩
    · rintro (old | ⟨p, (rfl | member), supported⟩)
      · exact Or.inl (Or.inl old)
      · exact Or.inl (Or.inr supported)
      · exact Or.inr ⟨p, member, supported⟩

theorem scan_language (phases : List (FiniteBlockPhase α)) (word : List α) :
    word ∈ (scan phases).language ↔ ∃ phase ∈ phases, word ∈ phase.language := by
  rw [scan, foldl_language, empty_language]
  simp


theorem foldl_width (phases : List (FiniteBlockPhase α)) (initial : FiniteBlockPhase α) :
    (phases.foldl combine initial).width = initial.width + (phases.map (fun phase => phase.width + 1)).sum := by
  induction phases generalizing initial with
  | nil => simp
  | cons phase rest ih =>
    rw [List.foldl_cons, ih]
    simp only [List.map_cons, List.sum_cons]
    omega

theorem scan_width (phases : List (FiniteBlockPhase α)) :
    (scan phases).width = (phases.map (fun phase => phase.width + 1)).sum := by
  rw [scan, foldl_width]
  simp


noncomputable def successMass (phase : FiniteBlockPhase α) : ℝ≥0∞ :=
  fairBlockMeasure phase.width (OptionPhase.success phase.value)

theorem concatenate_success (first second : FiniteBlockPhase α) :
    (concatenate first second).successMass = first.successMass * second.successMass := by
  have product := OptionPhase.append_success_measure (fairBlockMeasure first.width)
    (fairBlockMeasure second.width) first.value second.value
  rw [← fairBlockMeasure_map_splitBitVector,
    Measure.map_apply (measurable_of_countable _) (Set.to_countable _ |>.measurableSet)] at product
  exact product

theorem combine_success_ge_left (first second : FiniteBlockPhase α) :
    first.successMass ≤ (combine first second).successMass :=
  OptionPhase.bitFairOffer_success_ge_left first.width second.width first.value second.value

theorem combine_success_ge_right (first second : FiniteBlockPhase α) :
    second.successMass ≤ (combine first second).successMass :=
  OptionPhase.bitFairOffer_success_ge_right first.width second.width first.value second.value

theorem foldl_success_ge_start (phases : List (FiniteBlockPhase α)) (initial : FiniteBlockPhase α) :
    initial.successMass ≤ (phases.foldl combine initial).successMass := by
  induction phases generalizing initial with
  | nil => exact le_rfl
  | cons phase rest ih => exact (combine_success_ge_left initial phase).trans (ih _)

theorem foldl_success_ge_member (phases : List (FiniteBlockPhase α)) (initial phase : FiniteBlockPhase α)
    (member : phase ∈ phases) : phase.successMass ≤ (phases.foldl combine initial).successMass := by
  induction phases generalizing initial with
  | nil => simp at member
  | cons first rest ih =>
    rcases List.mem_cons.mp member with rfl | remaining
    · exact (combine_success_ge_right initial phase).trans (foldl_success_ge_start rest _)
    · exact ih (combine initial first) remaining

theorem scan_success_ge_member (phases : List (FiniteBlockPhase α)) (phase : FiniteBlockPhase α)
    (member : phase ∈ phases) : phase.successMass ≤ (scan phases).successMass :=
  foldl_success_ge_member phases empty phase member

end FiniteBlockPhase

end ComplexityOfGenerators
