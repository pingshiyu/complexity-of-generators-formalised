import ComplexityOfGenerators.Foundations.FixedWidthCodec

/-! Bounded decoding of the binary coordinates in a configuration code.
The midpoint enumeration includes malformed bit strings. Consequently it is
not safe to expand their binary values into unbounded unary counters. Clamping
after every digit is exact below the coordinate bound and detects every
out-of-range value. -/

namespace ComplexityOfGenerators.FixedWidthCodec

/-- The update performed by the bounded unary decoder. -/
def boundedDigit (bound value : ℕ) (bit : Bool) : ℕ :=
  min bound (2 * value + if bit then 1 else 0)

theorem boundedDigit_clamp (bound value : ℕ) (bit : Bool) :
    boundedDigit bound (min bound value) bit = boundedDigit bound value bit := by
  unfold boundedDigit
  cases bit <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega

/-- The accumulator never exceeds the supplied bound, even for invalid codes. -/
theorem boundedFold_le (bound : ℕ) (bits : List Bool) (value : ℕ) (initial : value ≤ bound) :
    bits.foldl (boundedDigit bound) value ≤ bound := by
  induction bits generalizing value with
  | nil => exact initial
  | cons bit bits ih =>
      exact ih _ (Nat.min_le_left _ _)

theorem boundedFold_eq (bound : ℕ) (bits : List Bool) (value : ℕ) :
    bits.foldl (boundedDigit bound) (min bound value) =
      min bound (bits.foldl (fun n b => 2 * n + if b then 1 else 0) value) := by
  induction bits generalizing value with
  | nil => rfl
  | cons bit bits ih =>
      simp only [List.foldl_cons, boundedDigit_clamp]
      exact ih _

/-- The operational decoder reads a little-endian field in reverse order,
which is the order produced by the verified frame loader. -/
theorem binary_fold_reverse (bits : List Bool) (value : ℕ) :
    bits.reverse.foldl (fun n b => 2 * n + if b then 1 else 0) value =
      2 ^ bits.length * value + Complexity.binValLE bits := by
  induction bits with
  | nil => simp [Complexity.binValLE]
  | cons bit bits ih =>
      simp only [List.reverse_cons, List.foldl_append, List.foldl_cons, List.foldl_nil,
        ih, List.length_cons, pow_succ, Complexity.binValLE]
      split_ifs <;> ring

theorem bounded_decode_eq (bound : ℕ) (bits : List Bool) :
    bits.reverse.foldl (boundedDigit bound) 0 = min bound (Complexity.binValLE bits) := by
  have h := boundedFold_eq bound bits.reverse 0
  simpa only [Nat.min_zero, binary_fold_reverse, Nat.mul_zero, Nat.zero_add] using h

/-- Saturation is a rejecting value. Testing strict inequality after clamping
is equivalent to the exact range test in `FixedWidthCodec.fin`. -/
theorem bounded_decode_valid (bound : ℕ) (bits : List Bool) :
    bits.reverse.foldl (boundedDigit bound) 0 < bound ↔ Complexity.binValLE bits < bound := by
  rw [bounded_decode_eq]
  omega

theorem fin_decode_eq_some_iff (bound : ℕ) (bits : List Bool) (value : Fin bound) :
    (fin bound).decode bits = some value ↔
      bits.length = bound ∧ bits.reverse.foldl (boundedDigit bound) 0 = value.val := by
  simp only [fin, bounded_decode_eq]
  split_ifs with h
  · simp only [Option.some.injEq, Fin.ext_iff]
    have small := h.2
    rw [Nat.min_eq_right (Nat.le_of_lt small)]
    exact ⟨fun eq => ⟨h.1, eq⟩, fun eq => eq.2⟩
  · simp only [reduceCtorEq, false_iff, not_and]
    intro length eq
    have small := value.isLt
    have : Complexity.binValLE bits < bound := by omega
    exact h ⟨length, by omega⟩

end ComplexityOfGenerators.FixedWidthCodec
