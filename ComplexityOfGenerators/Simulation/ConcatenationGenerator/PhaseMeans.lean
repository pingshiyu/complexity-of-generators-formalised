import ComplexityOfGenerators.Foundations.FiniteBlockPhaseLists
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Components
import ComplexityOfGenerators.Proofs.PolynomialConcatenationSupport

/-! The existing native concatenation scan is a fold of independent finite
candidate phases and fair flag-only offers. -/

namespace ComplexityOfGenerators.Simulation.ConcatenationGenerator

open MeasureTheory
open scoped ENNReal

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

abbrev sourcePhase (M : Machine Unit Bool α) (seed time : PolynomialBound) (index : ℕ) : FiniteBlockPhase α :=
  FiniteBlockPhase.fromList (seed index) (UnionGenerator.sourceValue M time index)

abbrev candidatePhase (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n j : ℕ) : FiniteBlockPhase α :=
  FiniteBlockPhase.concatenate (sourcePhase G leftSeed leftTime j) (sourcePhase H rightSeed rightTime (n - j))

def scanPhase (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) : FiniteBlockPhase α :=
  FiniteBlockPhase.scan ((List.range (n + 1)).map (candidatePhase G H leftSeed leftTime rightSeed rightTime n))

theorem pairValue_eq_append (first second : Option (List α)) :
    pairValue first second = OptionPhase.append first second := by
  cases first <;> cases second <;> rfl

theorem offer_eq_fairOffer (previous candidate : Option (List α)) (coin : Bool) :
    offer previous candidate coin = OptionPhase.fairOffer coin previous candidate := by
  cases previous <;> cases candidate <;> cases coin <;> rfl

theorem candidatePhase_evaluate (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (bits : BitString) (enough : leftSeed j + rightSeed (n - j) ≤ bits.length) :
    (candidatePhase G H leftSeed leftTime rightSeed rightTime n j).evaluate bits =
      pairValue (UnionGenerator.sourceValue G leftTime j (bits.take (leftSeed j)))
        (UnionGenerator.sourceValue H rightTime (n - j) ((bits.drop (leftSeed j)).take (rightSeed (n - j)))) := by
  rw [FiniteBlockPhase.evaluate_concatenate _ _ bits enough]
  rw [FiniteBlockPhase.evaluate_fromList _ _ bits (by omega),
    FiniteBlockPhase.evaluate_fromList _ _ (bits.drop (leftSeed j)) (by simp; omega)]
  exact (pairValue_eq_append _ _).symm

theorem next_phase_prefix (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (initial : FiniteBlockPhase α) (bits : BitString)
    (enough : (FiniteBlockPhase.combine initial (candidatePhase G H leftSeed leftTime rightSeed rightTime n j)).width ≤ bits.length) :
    next G H leftSeed leftTime rightSeed rightTime n j (initial.evaluate bits, bits.drop initial.width) =
      ((FiniteBlockPhase.combine initial (candidatePhase G H leftSeed leftTime rightSeed rightTime n j)).evaluate bits,
        bits.drop (FiniteBlockPhase.combine initial (candidatePhase G H leftSeed leftTime rightSeed rightTime n j)).width) := by
  let candidate := candidatePhase G H leftSeed leftTime rightSeed rightTime n j
  apply Eq.trans _ (FiniteBlockPhase.next_prefix initial candidate bits enough)
  have candidateFits : leftSeed j + rightSeed (n - j) ≤ (bits.drop initial.width).length := by
    simp only [List.length_drop]
    change initial.width + (leftSeed j + rightSeed (n - j) + 1) ≤ bits.length at enough
    omega
  change next G H leftSeed leftTime rightSeed rightTime n j (initial.evaluate bits, bits.drop initial.width) =
    FiniteBlockPhase.next candidate (initial.evaluate bits, bits.drop initial.width)
  simp only [next, FiniteBlockPhase.next]
  rw [candidatePhase_evaluate G H leftSeed leftTime rightSeed rightTime n j _ candidateFits,
    offer_eq_fairOffer]
  simp only [candidate, List.drop_drop, Nat.add_assoc]

theorem foldl_phase_prefix (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (indices : List ℕ) (initial : FiniteBlockPhase α) (bits : BitString)
    (enough : ((indices.map (candidatePhase G H leftSeed leftTime rightSeed rightTime n)).foldl
      FiniteBlockPhase.combine initial).width ≤ bits.length) :
    indices.foldl (fun state j => next G H leftSeed leftTime rightSeed rightTime n j state)
      (initial.evaluate bits, bits.drop initial.width) =
      (((indices.map (candidatePhase G H leftSeed leftTime rightSeed rightTime n)).foldl
        FiniteBlockPhase.combine initial).evaluate bits,
        bits.drop ((indices.map (candidatePhase G H leftSeed leftTime rightSeed rightTime n)).foldl
          FiniteBlockPhase.combine initial).width) := by
  induction indices generalizing initial with
  | nil => rfl
  | cons j rest ih =>
    simp only [List.map_cons, List.foldl_cons] at enough ⊢
    rw [next_phase_prefix G H leftSeed leftTime rightSeed rightTime n j initial bits
      ((FiniteBlockPhase.foldl_width_mono _ _).trans enough)]
    exact ih _ enough

theorem algorithm_eq_scanPhase (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (bits : BitString)
    (enough : (scanPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ bits.length) :
    algorithm G H leftSeed leftTime rightSeed rightTime n bits =
      (scanPhase G H leftSeed leftTime rightSeed rightTime n).evaluate bits := by
  have same := foldl_phase_prefix G H leftSeed leftTime rightSeed rightTime n (List.range (n + 1))
    FiniteBlockPhase.empty bits enough
  simpa only [FiniteBlockPhase.evaluate_empty, FiniteBlockPhase.empty, List.drop_zero, algorithm,
    scanPhase, FiniteBlockPhase.scan] using congrArg Prod.fst same

theorem scanPhase_mean (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ)
    (left : ∀ j ≤ n, (sourcePhase G leftSeed leftTime j).HasMean j)
    (right : ∀ j ≤ n, (sourcePhase H rightSeed rightTime j).HasMean j) :
    (scanPhase G H leftSeed leftTime rightSeed rightTime n).HasMean n := by
  change (FiniteBlockPhase.scan ((List.range (n + 1)).map
    (candidatePhase G H leftSeed leftTime rightSeed rightTime n))).HasMean n
  apply FiniteBlockPhase.scan_mean
  intro phase phaseMember
  obtain ⟨j, jMember, rfl⟩ := List.mem_map.mp phaseMember
  have within : j ≤ n := by have := List.mem_range.mp jMember; omega
  have sum : j + (n - j) = n := by omega
  simpa only [sum] using FiniteBlockPhase.concatenate_mean
    (sourcePhase G leftSeed leftTime j) (sourcePhase H rightSeed rightTime (n - j)) j (n - j)
    (left j within) (right (n - j) (by omega))

/-- The native concatenation algorithm's bounded output has the exact raw
first moment n times its success probability on every sufficient fair block. -/
theorem algorithm_mean (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (scanPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width)
    (left : ∀ j ≤ n, (sourcePhase G leftSeed leftTime j).HasMean j)
    (right : ∀ j ≤ n, (sourcePhase H rightSeed rightTime j).HasMean j) :
    OptionPhase.HasMean (fairBlockMeasure width)
      (fun bits => algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)) n := by
  have balanced := scanPhase_mean G H leftSeed leftTime rightSeed rightTime n left right
  have values : ∀ bits : Fin width → Bool, algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits) =
      (scanPhase G H leftSeed leftTime rightSeed rightTime n).evaluate (List.ofFn bits) := by
    intro bits
    exact algorithm_eq_scanPhase G H leftSeed leftTime rightSeed rightTime n _ (by simpa using fits)
  simpa only [values] using FiniteBlockPhase.evaluate_mean
    (scanPhase G H leftSeed leftTime rightSeed rightTime n) width n fits balanced

theorem scanPhase_width (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) :
    (scanPhase G H leftSeed leftTime rightSeed rightTime n).width =
      blocksSize leftSeed rightSeed n (List.range (n + 1)) := by
  rw [scanPhase, FiniteBlockPhase.scan_width]
  simp only [List.map_map]
  rfl

theorem scanPhase_width_le (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) :
    (scanPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ concatSeed leftSeed rightSeed n := by
  rw [scanPhase_width]
  exact totalBlocks_le leftSeed rightSeed n

theorem algorithm_mean_full_seed (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ)
    (left : ∀ j ≤ n, (sourcePhase G leftSeed leftTime j).HasMean j)
    (right : ∀ j ≤ n, (sourcePhase H rightSeed rightTime j).HasMean j) :
    OptionPhase.HasMean (fairBlockMeasure (concatSeed leftSeed rightSeed n))
      (fun bits => algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)) n :=
  algorithm_mean G H leftSeed leftTime rightSeed rightTime n _
    (scanPhase_width_le G H leftSeed leftTime rightSeed rightTime n) left right

theorem algorithm_event_measure (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (scanPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width)
    (event : Option (List α) → Prop) :
    fairBlockMeasure width {bits | event (algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits))} =
      fairBlockMeasure (scanPhase G H leftSeed leftTime rightSeed rightTime n).width
        {bits | event ((scanPhase G H leftSeed leftTime rightSeed rightTime n).value bits)} := by
  have values : ∀ bits : Fin width → Bool, algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits) =
      (scanPhase G H leftSeed leftTime rightSeed rightTime n).evaluate (List.ofFn bits) := by
    intro bits
    exact algorithm_eq_scanPhase G H leftSeed leftTime rightSeed rightTime n _ (by simpa using fits)
  simpa only [values] using FiniteBlockPhase.evaluate_event_measure
    (scanPhase G H leftSeed leftTime rightSeed rightTime n) width fits event

theorem scanPhase_language (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) (word : List α) :
    word ∈ (scanPhase G H leftSeed leftTime rightSeed rightTime n).language ↔
      ∃ j ≤ n, ∃ left right, left ∈ (sourcePhase G leftSeed leftTime j).language ∧
        right ∈ (sourcePhase H rightSeed rightTime (n - j)).language ∧ left ++ right = word := by
  rw [scanPhase, FiniteBlockPhase.scan_language]
  constructor
  · rintro ⟨phase, member, supported⟩
    obtain ⟨j, jMember, rfl⟩ := List.mem_map.mp member
    have index : j ≤ n := by have := List.mem_range.mp jMember; omega
    exact ⟨j, index, (FiniteBlockPhase.concatenate_language _ _ word).mp supported⟩
  · rintro ⟨j, index, left, right, leftMember, rightMember, wordEq⟩
    refine ⟨candidatePhase G H leftSeed leftTime rightSeed rightTime n j,
      List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩, ?_⟩
    exact (FiniteBlockPhase.concatenate_language _ _ word).mpr ⟨left, right, leftMember, rightMember, wordEq⟩

/-- Full support of every valid split is retained by the actual fair-offer
scan, and padding after its final coin changes no output probabilities. -/
theorem algorithm_word_probability (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n width : ℕ)
    (fits : (scanPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width) (word : List α) :
    (0 < fairBlockMeasure width {bits |
      algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits) = some word}) ↔
      ∃ j ≤ n, ∃ left right, left ∈ (sourcePhase G leftSeed leftTime j).language ∧
        right ∈ (sourcePhase H rightSeed rightTime (n - j)).language ∧ left ++ right = word := by
  rw [algorithm_event_measure G H leftSeed leftTime rightSeed rightTime n width fits (fun answer => answer = some word)]
  exact scanPhase_language G H leftSeed leftTime rightSeed rightTime n word


theorem scanPhase_success_ge_split (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (within : j ≤ n) :
    (sourcePhase G leftSeed leftTime j).successMass * (sourcePhase H rightSeed rightTime (n - j)).successMass ≤
      (scanPhase G H leftSeed leftTime rightSeed rightTime n).successMass := by
  rw [← FiniteBlockPhase.concatenate_success]
  exact FiniteBlockPhase.scan_success_ge_member _ (candidatePhase G H leftSeed leftTime rightSeed rightTime n j)
    (List.mem_map.mpr ⟨j, List.mem_range.mpr (by omega), rfl⟩)

/-- Trying every split loses no factor of success probability: the scan
succeeds whenever this particular independent source pair succeeds. -/
theorem algorithm_success_ge_split (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n width j : ℕ) (fits : (scanPhase G H leftSeed leftTime rightSeed rightTime n).width ≤ width) (within : j ≤ n) :
    (sourcePhase G leftSeed leftTime j).successMass * (sourcePhase H rightSeed rightTime (n - j)).successMass ≤
      fairBlockMeasure width {bits | (algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)).isSome} := by
  rw [algorithm_event_measure G H leftSeed leftTime rightSeed rightTime n width fits (fun answer => answer.isSome = true)]
  exact scanPhase_success_ge_split G H leftSeed leftTime rightSeed rightTime n j within

theorem algorithm_success_ge_split_full_seed (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (within : j ≤ n) :
    (sourcePhase G leftSeed leftTime j).successMass * (sourcePhase H rightSeed rightTime (n - j)).successMass ≤
      fairBlockMeasure (concatSeed leftSeed rightSeed n) {bits |
        (algorithm G H leftSeed leftTime rightSeed rightTime n (List.ofFn bits)).isSome} :=
  algorithm_success_ge_split G H leftSeed leftTime rightSeed rightTime n _ j
    (scanPhase_width_le G H leftSeed leftTime rightSeed rightTime n) within

end ComplexityOfGenerators.Simulation.ConcatenationGenerator
