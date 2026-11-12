import Mathlib.Data.Nat.Log

/-! Executable little-endian fixed-width Boolean blocks. The same codec is
used by graph certificate labels and bounded rational selection. -/

namespace ComplexityOfGenerators.FixedBitBlocks

def encode : ℕ → ℕ → List Bool
  | 0, _ => []
  | count + 1, value => decide (value % 2 = 1) :: encode count (value / 2)

def decode : List Bool → ℕ
  | [] => 0
  | bit :: rest => bit.toNat + 2 * decode rest

@[simp] theorem encode_length (count value : ℕ) : (encode count value).length = count := by
  induction count generalizing value with
  | zero => rfl
  | succ count ih => simp [encode, ih]

theorem decode_encode (count value : ℕ) (bound : value < 2 ^ count) :
    decode (encode count value) = value := by
  induction count generalizing value with
  | zero =>
    have zero : value = 0 := by simpa using bound
    subst value
    rfl
  | succ count ih =>
    have half : value / 2 < 2 ^ count := by rw [Nat.pow_succ] at bound; omega
    rw [encode, decode, ih (value / 2) half]
    have parity : value % 2 = 0 ∨ value % 2 = 1 := by omega
    rcases parity with parity | parity <;> simp [parity] <;> omega

theorem decode_bound (bits : List Bool) : decode bits < 2 ^ bits.length := by
  induction bits with
  | nil => simp [decode]
  | cons bit rest ih =>
    simp only [decode, List.length_cons, Nat.pow_succ]
    cases bit <;> simp <;> omega

theorem encode_decode (bits : List Bool) : encode bits.length (decode bits) = bits := by
  induction bits with
  | nil => rfl
  | cons bit rest ih =>
    have half : (bit.toNat + 2 * decode rest) / 2 = decode rest := by
      cases bit
      · simp
      · simp only [Bool.toNat_true]; omega
    have parity : decide ((bit.toNat + 2 * decode rest) % 2 = 1) = bit := by
      cases bit <;> simp
    simp only [List.length_cons, decode, encode, half, parity, ih]

theorem decode_injective {bits other : List Bool} (length : bits.length = other.length)
    (value : decode bits = decode other) : bits = other := by
  rw [← encode_decode bits, ← encode_decode other, length, value]

theorem decode_append (bits other : List Bool) :
    decode (bits ++ other) = decode bits + 2 ^ bits.length * decode other := by
  induction bits with
  | nil => simp [decode]
  | cons bit rest ih =>
    simp [decode, ih, Nat.pow_succ, Nat.mul_add, Nat.mul_assoc,
      Nat.add_left_comm, Nat.add_comm, Nat.mul_comm]

theorem decode_take_succ (bits : List Bool) (count : ℕ) (bound : count < bits.length) :
    decode (bits.take (count + 1)) =
      decode (bits.take count) + 2 ^ count * bits[count].toNat := by
  rw [List.take_add_one, List.getElem?_eq_getElem bound]
  change decode (bits.take count ++ [bits[count]]) = _
  rw [decode_append]
  simp only [decode, List.length_take, Nat.min_eq_left (Nat.le_of_lt bound),
    Nat.mul_zero, Nat.add_zero]

/-- The block codec is a bijection with the 2^b integer choices used by finite
uniform probability arguments. -/
def blockEquiv (count : ℕ) : {bits : List Bool // bits.length = count} ≃ Fin (2 ^ count) where
  toFun := fun bits => ⟨decode bits.val, by
    have bound := decode_bound bits.val
    simpa [bits.property] using bound⟩
  invFun := fun value => ⟨encode count value.val, encode_length count value.val⟩
  left_inv := by
    intro bits
    apply Subtype.ext
    change encode count (decode bits.val) = bits.val
    simpa only [bits.property] using encode_decode bits.val
  right_inv := by
    intro value
    apply Fin.ext
    exact decode_encode count value.val value.isLt

end ComplexityOfGenerators.FixedBitBlocks
