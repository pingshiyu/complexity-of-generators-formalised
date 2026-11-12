import ComplexityOfGenerators.Examples.HAMPATHBounds
import ComplexityOfGenerators.Foundations.FixedBitBlocks

/-!
Fixed-width binary next-vertex labels for the concrete HAMPATH reduction.
The codec is little endian; the manuscript only fixes the width, so the bit
order has no effect on the certificate or rank equations. Out-of-range labels
and separator symbols are rejected by the decoder.
-/

namespace ComplexityOfGenerators.Examples.HAMPATH

set_option backward.isDefEq.respectTransparency false

def encodeBits (count value : ℕ) : List Symbol :=
  (FixedBitBlocks.encode count value).map Symbol.bit

def decodeBits : List Symbol → Option ℕ
  | [] => some 0
  | .separator :: _ => none
  | .bit b :: rest => do
      let value ← decodeBits rest
      pure (b.toNat + 2 * value)

@[simp] theorem encodeBits_length (count value : ℕ) :
    (encodeBits count value).length = count := by simp [encodeBits]

theorem decodeBits_map (bits : List Bool) :
    decodeBits (bits.map Symbol.bit) = some (FixedBitBlocks.decode bits) := by
  induction bits with
  | nil => rfl
  | cons bit rest ih => simp [decodeBits, ih, FixedBitBlocks.decode]

theorem decodeBits_encode (count value : ℕ) (bound : value < 2 ^ count) :
    decodeBits (encodeBits count value) = some value := by
  rw [encodeBits, decodeBits_map, FixedBitBlocks.decode_encode count value bound]

theorem decodeBits_sound (word : List Symbol) (value : ℕ)
    (decoded : decodeBits word = some value) :
    ∃ bits : List Bool, word = bits.map Symbol.bit ∧ FixedBitBlocks.decode bits = value := by
  induction word generalizing value with
  | nil => simp [decodeBits] at decoded; subst value; exact ⟨[], rfl, rfl⟩
  | cons head rest ih =>
    cases head with
    | separator => simp [decodeBits] at decoded
    | bit b =>
      cases tail : decodeBits rest with
      | none => simp [decodeBits, tail] at decoded
      | some n =>
        obtain ⟨bits, equal, number⟩ := ih n tail
        simp [decodeBits, tail] at decoded
        subst value
        exact ⟨b :: bits, by simp [equal], by simp [FixedBitBlocks.decode, number]⟩

theorem decodeBits_bound (word : List Symbol) (value : ℕ)
    (decoded : decodeBits word = some value) : value < 2 ^ word.length := by
  obtain ⟨bits, rfl, rfl⟩ := decodeBits_sound word value decoded
  simpa using FixedBitBlocks.decode_bound bits

theorem encodeBits_decode (word : List Symbol) (value : ℕ)
    (decoded : decodeBits word = some value) : encodeBits word.length value = word := by
  obtain ⟨bits, rfl, rfl⟩ := decodeBits_sound word value decoded
  simp [encodeBits, FixedBitBlocks.encode_decode]

def vertexLabel (size vertex : ℕ) : List Symbol := encodeBits (width size) vertex

def decodeLabel (size : ℕ) (label : List Symbol) : Option ℕ := do
  if label.length = width size then
    let vertex ← decodeBits label
    if vertex < size then some vertex else none
  else none

@[simp] theorem vertexLabel_length (size vertex : ℕ) :
    (vertexLabel size vertex).length = width size := by simp [vertexLabel]

theorem decodeLabel_encode {size vertex : ℕ} (bound : vertex < size) :
    decodeLabel size (vertexLabel size vertex) = some vertex := by
  have fits : vertex < 2 ^ width size :=
    bound.trans_le (Nat.le_pow_clog (by decide : 1 < 2) size)
  simp [decodeLabel, vertexLabel, decodeBits_encode _ _ fits, bound]

theorem decodeLabel_sound (size : ℕ) (label : List Symbol) (vertex : ℕ)
    (decoded : decodeLabel size label = some vertex) :
    vertex < size ∧ label = vertexLabel size vertex := by
  unfold decodeLabel at decoded
  split_ifs at decoded with length
  cases bits : decodeBits label with
  | none => simp [bits] at decoded
  | some n =>
    rw [bits] at decoded
    change (if n < size then some n else none) = some vertex at decoded
    split_ifs at decoded with bound
    have equal : n = vertex := Option.some.inj decoded
    subst n
    exact ⟨bound, by simpa [vertexLabel, length] using (encodeBits_decode label vertex bits).symm⟩

theorem vertexLabel_injective {size : ℕ} {v w : ℕ} (vBound : v < size) (wBound : w < size)
    (equal : vertexLabel size v = vertexLabel size w) : v = w := by
  have same := congrArg (decodeLabel size) equal
  rw [decodeLabel_encode vBound, decodeLabel_encode wBound] at same
  exact Option.some.inj same

end ComplexityOfGenerators.Examples.HAMPATH
