import ComplexityOfGenerators.Foundations.BalancedPairProbability

/-! First-moment identities for finite independent optional-output phases.
Selection uses only success flags; successful empty words retain their flags. -/

namespace ComplexityOfGenerators.OptionPhase

open MeasureTheory
open scoped ENNReal
open BalancedPairPhase (optionLength)

variable {X Y α : Type} [MeasurableSpace X] [MeasurableSpace Y]
    [MeasurableSingletonClass X] [MeasurableSingletonClass Y] [Countable X] [Countable Y]

def success (f : X → Option (List α)) : Set X := {x | (f x).isSome}
def failure (f : X → Option (List α)) : Set X := {x | f x = none}

def HasMean (μ : Measure X) (f : X → Option (List α)) (target : ℕ) : Prop :=
  (∫⁻ x, (optionLength (f x) : ℝ≥0∞) ∂μ) = (target : ℝ≥0∞) * μ (success f)

def offer (first second : Option (List α)) : Option (List α) :=
  match first with
  | some word => some word
  | none => second

@[simp] theorem offer_eq_or (first second : Option (List α)) : offer first second = first.or second := by
  cases first <;> rfl

theorem offer_success_measure (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → Option (List α)) (g : Y → Option (List α)) :
    (μ.prod ν) (success (fun pair => offer (f pair.1) (g pair.2))) =
      μ (success f) + ν (success g) * μ (failure f) := by
  classical
  rw [Measure.prod_apply (Set.to_countable _ |>.measurableSet)]
  have inner : ∀ x, ν {y | (x, y) ∈ success (fun pair => offer (f pair.1) (g pair.2))} =
      (success f).indicator (fun _ => (1 : ℝ≥0∞)) x +
        (failure f).indicator (fun _ => ν (success g)) x := by
    intro x
    cases value : f x with
    | none => simp [success, failure, offer, value]
    | some word => simp [success, failure, offer, value]
  change (∫⁻ x, ν {y | (x, y) ∈ success (fun pair => offer (f pair.1) (g pair.2))} ∂μ) = _
  simp_rw [inner]
  rw [lintegral_add_left (measurable_of_countable _),
    lintegral_indicator_const (Set.to_countable _ |>.measurableSet),
    lintegral_indicator_const (Set.to_countable _ |>.measurableSet), one_mul]

theorem offer_length_integral (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → Option (List α)) (g : Y → Option (List α)) :
    (∫⁻ pair, (optionLength (offer (f pair.1) (g pair.2)) : ℝ≥0∞) ∂μ.prod ν) =
      (∫⁻ x, (optionLength (f x) : ℝ≥0∞) ∂μ) +
        (∫⁻ y, (optionLength (g y) : ℝ≥0∞) ∂ν) * μ (failure f) := by
  classical
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  have inner : ∀ x, (∫⁻ y, (optionLength (offer (f x) (g y)) : ℝ≥0∞) ∂ν) =
      (optionLength (f x) : ℝ≥0∞) +
        (failure f).indicator (fun _ => ∫⁻ y, (optionLength (g y) : ℝ≥0∞) ∂ν) x := by
    intro x
    cases value : f x with
    | none => simp [failure, offer, value, optionLength]
    | some word => simp [failure, offer, value, optionLength]
  simp_rw [inner]
  rw [lintegral_add_left (measurable_of_countable _),
    lintegral_indicator_const (Set.to_countable _ |>.measurableSet)]

/-- Independent flag-only fallback preserves a common conditional mean. -/
theorem HasMean.offer (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → Option (List α)) (g : Y → Option (List α)) (target : ℕ)
    (first : HasMean μ f target) (second : HasMean ν g target) :
    HasMean (μ.prod ν) (fun pair => offer (f pair.1) (g pair.2)) target := by
  rw [HasMean, offer_length_integral, offer_success_measure, first, second]
  ring

def append (first second : Option (List α)) : Option (List α) := do
  let left ← first
  let right ← second
  return left ++ right

theorem append_success_measure (μ : Measure X) (ν : Measure Y)
    (f : X → Option (List α)) (g : Y → Option (List α)) :
    (μ.prod ν) (success (fun pair => append (f pair.1) (g pair.2))) =
      μ (success f) * ν (success g) := by
  have event : success (fun pair => append (f pair.1) (g pair.2)) = success f ×ˢ success g := by
    ext pair
    cases first : f pair.1 <;> cases second : g pair.2 <;> simp [success, append, first, second]
  rw [event, Measure.prod_prod]

theorem append_length_integral (μ : Measure X) (ν : Measure Y)
    (f : X → Option (List α)) (g : Y → Option (List α)) :
    (∫⁻ pair, (optionLength (append (f pair.1) (g pair.2)) : ℝ≥0∞) ∂μ.prod ν) =
      (∫⁻ x, (optionLength (f x) : ℝ≥0∞) ∂μ) * ν (success g) +
        (∫⁻ y, (optionLength (g y) : ℝ≥0∞) ∂ν) * μ (success f) := by
  classical
  have length : ∀ x y, (optionLength (append (f x) (g y)) : ℝ≥0∞) =
      (success g).indicator (fun _ => (optionLength (f x) : ℝ≥0∞)) y +
        (success f).indicator (fun _ => (optionLength (g y) : ℝ≥0∞)) x := by
    intro x y
    cases first : f x <;> cases second : g y <;>
      simp [success, append, first, second, optionLength, Nat.cast_add]
  rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp_rw [length, lintegral_add_left (measurable_of_countable _),
    lintegral_indicator_const (Set.to_countable _ |>.measurableSet)]
  have inner : ∀ x, (∫⁻ y, (success f).indicator (fun _ => (optionLength (g y) : ℝ≥0∞)) x ∂ν) =
      (success f).indicator (fun _ => ∫⁻ y, (optionLength (g y) : ℝ≥0∞) ∂ν) x := by
    intro x
    by_cases member : x ∈ success f
    · simp only [Set.indicator_of_mem member]
    · simp [Set.indicator_of_notMem member]
  simp_rw [inner]
  rw [lintegral_mul_const _ (measurable_of_countable _),
    lintegral_indicator_const (Set.to_countable _ |>.measurableSet)]

/-- Successful concatenation adds the two conditional output-length means. -/
theorem HasMean.append (μ : Measure X) (ν : Measure Y)
    (f : X → Option (List α)) (g : Y → Option (List α)) (firstTarget secondTarget : ℕ)
    (first : HasMean μ f firstTarget) (second : HasMean ν g secondTarget) :
    HasMean (μ.prod ν) (fun pair => append (f pair.1) (g pair.2)) (firstTarget + secondTarget) := by
  rw [HasMean, append_length_integral, append_success_measure, first, second, Nat.cast_add]
  ring


/-- A fresh choice among phases with the same target mean preserves that
mean, including when their success probabilities differ. -/
theorem HasMean.mixture {J : Type} [MeasurableSpace J] [MeasurableSingletonClass J] [Countable J]
    (ρ : Measure J) (μ : Measure X) (f : J → X → Option (List α)) (target : ℕ)
    (balanced : ∀ j, HasMean μ (f j) target) :
    HasMean (ρ.prod μ) (fun pair => f pair.1 pair.2) target := by
  rw [HasMean, lintegral_prod _ (measurable_of_countable _).aemeasurable]
  change ∀ j, (∫⁻ x, (optionLength (f j x) : ℝ≥0∞) ∂μ) = (target : ℝ≥0∞) * μ (success (f j)) at balanced
  change (∫⁻ j, ∫⁻ x, (optionLength (f j x) : ℝ≥0∞) ∂μ ∂ρ) = _
  simp_rw [balanced]
  rw [Measure.prod_apply (Set.to_countable _ |>.measurableSet),
    lintegral_const_mul _ (measurable_of_countable _)]
  rfl

theorem HasMean.swap (μ : Measure X) (ν : Measure Y) [SFinite μ] [SFinite ν]
    (f : Y × X → Option (List α)) (target : ℕ) (balanced : HasMean (ν.prod μ) f target) :
    HasMean (μ.prod ν) (fun pair => f pair.swap) target := by
  have measure : (μ.prod ν) (success (fun pair => f pair.swap)) = (ν.prod μ) (success f) := by
    change (μ.prod ν) (Prod.swap ⁻¹' success f) = _
    rw [← Measure.map_apply measurable_swap (Set.to_countable _ |>.measurableSet), Measure.prod_swap]
  rw [HasMean, measure]
  calc
    (∫⁻ pair, (optionLength (f pair.swap) : ℝ≥0∞) ∂μ.prod ν) =
        ∫⁻ pair, (optionLength (f pair) : ℝ≥0∞) ∂ν.prod μ := by
      rw [← Measure.prod_swap (μ := μ) (ν := ν),
        lintegral_map (measurable_of_countable _) measurable_swap]
    _ = _ := balanced

def fairOffer (coin : Bool) (first second : Option (List α)) : Option (List α) :=
  if coin then offer second first else offer first second

/-- Fair-order fallback keeps the common target mean and gives both sources
an opportunity to supply the result even when the other always succeeds. -/
theorem HasMean.fairOffer (μ : Measure X) (ν : Measure Y)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → Option (List α)) (g : Y → Option (List α)) (target : ℕ)
    (first : HasMean μ f target) (second : HasMean ν g target) :
    HasMean ((PMF.uniformOfFintype Bool).toMeasure.prod (μ.prod ν))
      (fun pair => fairOffer pair.1 (f pair.2.1) (g pair.2.2)) target := by
  refine HasMean.mixture (PMF.uniformOfFintype Bool).toMeasure (μ.prod ν)
    (fun coin pair => OptionPhase.fairOffer coin (f pair.1) (g pair.2)) target ?_
  intro coin
  cases coin with
  | false => exact HasMean.offer μ ν f g target first second
  | true => exact HasMean.swap μ ν _ target (HasMean.offer ν μ g f target second first)


/-- A proved pushforward law transports a phase mean to its concrete input
representation; no independence or implementation premise is added. -/
theorem HasMean.pullback (μ : Measure X) (ν : Measure Y) (map : X → Y)
    (mapped : μ.map map = ν) (f : Y → Option (List α)) (target : ℕ)
    (balanced : HasMean ν f target) : HasMean μ (fun x => f (map x)) target := by
  have mass : μ (success (fun x => f (map x))) = ν (success f) := by
    change μ (map ⁻¹' success f) = _
    rw [← Measure.map_apply (measurable_of_countable _) (Set.to_countable _ |>.measurableSet), mapped]
  change (∫⁻ x, (optionLength (f (map x)) : ℝ≥0∞) ∂μ) = _
  rw [mass]
  calc
    (∫⁻ x, (optionLength (f (map x)) : ℝ≥0∞) ∂μ) =
        ∫⁻ y, (optionLength (f y) : ℝ≥0∞) ∂ν := by
      rw [← mapped, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    _ = _ := balanced


theorem fairOffer_success_measure (μ : Measure X) (ν : Measure Y)
    (f : X → Option (List α)) (g : Y → Option (List α)) :
    ((PMF.uniformOfFintype Bool).toMeasure.prod (μ.prod ν))
      (success (fun pair => OptionPhase.fairOffer pair.1 (f pair.2.1) (g pair.2.2))) =
        (μ.prod ν) (success (fun pair => offer (f pair.1) (g pair.2))) := by
  have event : success (fun pair : Bool × X × Y => OptionPhase.fairOffer pair.1 (f pair.2.1) (g pair.2.2)) =
      Set.univ ×ˢ success (fun pair : X × Y => offer (f pair.1) (g pair.2)) := by
    ext ⟨coin, x, y⟩
    cases coin <;> cases first : f x <;> cases second : g y <;>
      simp [success, OptionPhase.fairOffer, offer, first, second]
  rw [event, Measure.prod_prod, measure_univ, one_mul]

theorem fairOffer_success_ge_left (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure ν]
    (f : X → Option (List α)) (g : Y → Option (List α)) :
    μ (success f) ≤ ((PMF.uniformOfFintype Bool).toMeasure.prod (μ.prod ν))
      (success (fun pair => OptionPhase.fairOffer pair.1 (f pair.2.1) (g pair.2.2))) := by
  rw [fairOffer_success_measure, offer_success_measure]
  calc
    μ (success f) = μ (success f) + 0 := by simp
    _ ≤ μ (success f) + ν (success g) * μ (failure f) := by gcongr; exact bot_le

theorem fairOffer_success_ge_right (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ]
    (f : X → Option (List α)) (g : Y → Option (List α)) :
    ν (success g) ≤ ((PMF.uniformOfFintype Bool).toMeasure.prod (μ.prod ν))
      (success (fun pair => OptionPhase.fairOffer pair.1 (f pair.2.1) (g pair.2.2))) := by
  rw [fairOffer_success_measure]
  have subset : Set.univ ×ˢ success g ⊆ success (fun pair => offer (f pair.1) (g pair.2)) := by
    rintro ⟨x, y⟩ ⟨_, accepted⟩
    cases first : f x with
    | none => simpa only [success, offer, first, Set.mem_ofPred_eq] using accepted
    | some word => simp [success, offer, first]
  have bound := measure_mono (μ := μ.prod ν) subset
  simpa only [Measure.prod_prod, measure_univ, one_mul] using bound

end ComplexityOfGenerators.OptionPhase
