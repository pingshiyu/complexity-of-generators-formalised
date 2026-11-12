import ComplexityOfGenerators.Foundations.FiniteBlockProbability
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Input

/-! Exact probabilities for the executable bounded rational selector. -/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal
open Simulation.WordStack.RationalSelection

theorem choose_eq_true_iff (denominator numerator : ℕ) (ordered : numerator ≤ denominator)
    (bits : BitString) :
    choose denominator numerator bits = some true ↔
      FixedBitBlocks.decode (bits.take (Nat.clog 2 denominator)) < numerator := by
  simp only [choose]
  split_ifs with below
  · simp only [Option.some.injEq, decide_eq_true_eq]
  · simp only [false_iff]
    omega

theorem choose_eq_false_iff (denominator numerator : ℕ) (_ordered : numerator ≤ denominator)
    (bits : BitString) :
    choose denominator numerator bits = some false ↔
      numerator ≤ FixedBitBlocks.decode (bits.take (Nat.clog 2 denominator)) ∧
      FixedBitBlocks.decode (bits.take (Nat.clog 2 denominator)) < denominator := by
  simp only [choose]
  split_ifs with below
  · simp only [Option.some.injEq, decide_eq_false_iff_not, not_lt]
    exact ⟨fun h => ⟨h, below⟩, And.left⟩
  · simp only [false_iff]
    omega

theorem choose_isSome_iff (denominator numerator : ℕ) (bits : BitString) :
    (choose denominator numerator bits).isSome ↔
      FixedBitBlocks.decode (bits.take (Nat.clog 2 denominator)) < denominator := by
  simp only [choose]
  split_ifs <;> simp_all

theorem fairBlockMeasure_choose_true (width denominator numerator : ℕ)
    (large : 1 < denominator) (ordered : numerator ≤ denominator)
    (enough : Nat.clog 2 denominator ≤ width) :
    fairBlockMeasure width {bits | choose denominator numerator (List.ofFn bits) = some true} =
      (numerator : ℝ≥0∞) / ((2 ^ Nat.clog 2 denominator : ℕ) : ℝ≥0∞) := by
  have exponentPositive := Nat.clog_pos (by decide : 1 < 2) large
  have widthPositive : 0 < width := lt_of_lt_of_le exponentPositive enough
  have equal : {bits | choose denominator numerator (List.ofFn bits) = some true} =
      {bits | takeBitVector width (Nat.clog 2 denominator) enough bits ∈
        {short | FixedBitBlocks.decode (List.ofFn short) < numerator}} := by
    ext bits
    rw [Set.mem_ofPred_eq, choose_eq_true_iff denominator numerator ordered]
    simp only [Set.mem_ofPred_eq, ofFn_takeBitVector]
  rw [equal, fairBlockMeasure_prefix_event width _ widthPositive exponentPositive enough _
    (by exact Set.to_countable _ |>.measurableSet)]
  exact fairBlockMeasure_decode_below _ numerator
    (ordered.trans (Nat.le_pow_clog (by decide) denominator))

theorem fairBlockMeasure_choose_false (width denominator numerator : ℕ)
    (large : 1 < denominator) (ordered : numerator ≤ denominator)
    (enough : Nat.clog 2 denominator ≤ width) :
    fairBlockMeasure width {bits | choose denominator numerator (List.ofFn bits) = some false} =
      ((denominator - numerator : ℕ) : ℝ≥0∞) / ((2 ^ Nat.clog 2 denominator : ℕ) : ℝ≥0∞) := by
  have exponentPositive := Nat.clog_pos (by decide : 1 < 2) large
  have widthPositive : 0 < width := lt_of_lt_of_le exponentPositive enough
  have equal : {bits | choose denominator numerator (List.ofFn bits) = some false} =
      {bits | takeBitVector width (Nat.clog 2 denominator) enough bits ∈
        {short | numerator ≤ FixedBitBlocks.decode (List.ofFn short) ∧
          FixedBitBlocks.decode (List.ofFn short) < denominator}} := by
    ext bits
    rw [Set.mem_ofPred_eq, choose_eq_false_iff denominator numerator ordered]
    simp only [Set.mem_ofPred_eq, ofFn_takeBitVector]
  rw [equal, fairBlockMeasure_prefix_event width _ widthPositive exponentPositive enough _
    (by exact Set.to_countable _ |>.measurableSet)]
  exact fairBlockMeasure_decode_interval _ numerator denominator ordered (Nat.le_pow_clog (by decide) denominator)

theorem fairBlockMeasure_choose_success (width denominator numerator : ℕ)
    (large : 1 < denominator) (enough : Nat.clog 2 denominator ≤ width) :
    fairBlockMeasure width {bits | (choose denominator numerator (List.ofFn bits)).isSome} =
      (denominator : ℝ≥0∞) / ((2 ^ Nat.clog 2 denominator : ℕ) : ℝ≥0∞) := by
  have exponentPositive := Nat.clog_pos (by decide : 1 < 2) large
  have widthPositive : 0 < width := lt_of_lt_of_le exponentPositive enough
  have equal : {bits | (choose denominator numerator (List.ofFn bits)).isSome} =
      {bits | takeBitVector width (Nat.clog 2 denominator) enough bits ∈
        {short | FixedBitBlocks.decode (List.ofFn short) < denominator}} := by
    ext bits
    rw [Set.mem_ofPred_eq, choose_isSome_iff]
    simp only [Set.mem_ofPred_eq, ofFn_takeBitVector]
  rw [equal, fairBlockMeasure_prefix_event width _ widthPositive exponentPositive enough _
    (by exact Set.to_countable _ |>.measurableSet)]
  exact fairBlockMeasure_decode_below _ denominator (Nat.le_pow_clog (by decide) denominator)


theorem fairBlockMeasure_choose_success_ge_half (width denominator numerator : ℕ)
    (large : 1 < denominator) (enough : Nat.clog 2 denominator ≤ width) :
    (2 : ℝ≥0∞)⁻¹ ≤
      fairBlockMeasure width {bits | (choose denominator numerator (List.ofFn bits)).isSome} := by
  rw [fairBlockMeasure_choose_success width denominator numerator large enough]
  have denominatorPositive : (0 : ℝ≥0∞) < denominator := by exact_mod_cast (lt_trans (by decide : 0 < 1) large)
  have powerPositive : (0 : ℝ≥0∞) < (2 ^ Nat.clog 2 denominator : ℕ) := by positivity
  apply (ENNReal.le_div_iff_mul_le (Or.inl powerPositive.ne') (Or.inl (by simp))).2
  have bound : ((2 ^ Nat.clog 2 denominator : ℕ) : ℝ≥0∞) ≤ 2 * denominator := by
    exact_mod_cast pow_clog_le_twice denominator (by omega)
  calc
    (2 : ℝ≥0∞)⁻¹ * ((2 ^ Nat.clog 2 denominator : ℕ) : ℝ≥0∞) ≤
        (2 : ℝ≥0∞)⁻¹ * (2 * denominator) := by gcongr
    _ = denominator := by
      rw [← mul_assoc, ENNReal.inv_mul_cancel (by norm_num) (by norm_num), one_mul]

def chosenNat (lower upper : ℕ) (choice : Option Bool) : ℕ :=
  match choice with
  | some true => lower
  | some false => upper
  | none => 0

theorem lintegral_choose_length (width denominator numerator lower upper : ℕ)
    (large : 1 < denominator) (ordered : numerator ≤ denominator)
    (enough : Nat.clog 2 denominator ≤ width) :
    (∫⁻ bits, (chosenNat lower upper (choose denominator numerator (List.ofFn bits)) : ℝ≥0∞)
      ∂fairBlockMeasure width) =
      (lower : ℝ≥0∞) * ((numerator : ℝ≥0∞) / ((2 ^ Nat.clog 2 denominator : ℕ) : ℝ≥0∞)) +
      (upper : ℝ≥0∞) * (((denominator - numerator : ℕ) : ℝ≥0∞) /
        ((2 ^ Nat.clog 2 denominator : ℕ) : ℝ≥0∞)) := by
  classical
  have equal : (fun bits : Fin width → Bool => (chosenNat lower upper (choose denominator numerator (List.ofFn bits)) : ℝ≥0∞)) =
      fun bits => {bits | choose denominator numerator (List.ofFn bits) = some true}.indicator
          (fun _ => (lower : ℝ≥0∞)) bits +
        {bits | choose denominator numerator (List.ofFn bits) = some false}.indicator
          (fun _ => (upper : ℝ≥0∞)) bits := by
    funext bits
    cases result : choose denominator numerator (List.ofFn bits) with
    | none => simp [chosenNat, result]
    | some flag => cases flag <;> simp [chosenNat, result]
  rw [equal, lintegral_add_left (by fun_prop),
    lintegral_indicator_const (Set.to_countable _ |>.measurableSet),
    lintegral_indicator_const (Set.to_countable _ |>.measurableSet),
    fairBlockMeasure_choose_true width denominator numerator large ordered enough,
    fairBlockMeasure_choose_false width denominator numerator large ordered enough]

/-- The accepted portion of a strict bracketing selector has exactly the
requested first moment, even though its bounded draw can reject. -/
theorem lintegral_choose_bracketing (width lower target upper : ℕ)
    (below : lower < target) (above : target < upper)
    (enough : Nat.clog 2 (upper - lower) ≤ width) :
    (∫⁻ bits, (chosenNat lower upper (choose (upper - lower) (upper - target) (List.ofFn bits)) : ℝ≥0∞)
      ∂fairBlockMeasure width) =
      (target : ℝ≥0∞) *
        fairBlockMeasure width {bits | (choose (upper - lower) (upper - target) (List.ofFn bits)).isSome} := by
  have large : 1 < upper - lower := by omega
  have ordered : upper - target ≤ upper - lower := by omega
  rw [lintegral_choose_length width _ _ lower upper large ordered enough,
    fairBlockMeasure_choose_success width _ _ large enough]
  simp only [← mul_div_assoc]
  rw [← ENNReal.add_div]
  congr 1
  have identity : lower * (upper - target) + upper * ((upper - lower) - (upper - target)) = target * (upper - lower) := by
    have one : target + (upper - target) = upper := by omega
    have two : lower + (upper - lower) = upper := by omega
    have three : (upper - lower) - (upper - target) = target - lower := by omega
    have four : lower + (target - lower) = target := by omega
    rw [three]
    nlinarith
  exact_mod_cast identity

end ComplexityOfGenerators
