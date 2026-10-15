import Complexitylib.Classes.Containments.Internal.WitnessEnum
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic

/-!
# Effective fixed-width configuration encodings

These codecs compose field by field, so their widths add instead of growing
like the number of configurations. Binary counters and their round trips are
reused from Complexitylib. No enumeration of an entire configuration type is
needed to encode or decode a vertex.
-/

namespace ComplexityOfGenerators

/-- An effective representation with a fixed bit width and a proved round trip.
Decoders may reject malformed strings. -/
structure FixedWidthCodec (V : Type) where
  width : ℕ
  encode : V → List Bool
  decode : List Bool → Option V
  encode_length : ∀ v, (encode v).length = width
  decode_encode : ∀ v, decode (encode v) = some v

namespace FixedWidthCodec

variable {V W : Type}

/-- Transport a codec along an explicit equivalence. -/
def transport (c : FixedWidthCodec V) (e : V ≃ W) : FixedWidthCodec W where
  width := c.width
  encode w := c.encode (e.symm w)
  decode bits := (c.decode bits).map e
  encode_length w := c.encode_length _
  decode_encode w := by simp [c.decode_encode]

/-- Concatenated fields have additive width. -/
def prod (c : FixedWidthCodec V) (d : FixedWidthCodec W) : FixedWidthCodec (V × W) where
  width := c.width + d.width
  encode v := c.encode v.1 ++ d.encode v.2
  decode bits := do
    let v ← c.decode (bits.take c.width)
    let w ← d.decode (bits.drop c.width)
    pure (v, w)
  encode_length v := by simp [c.encode_length, d.encode_length]
  decode_encode v := by
    rw [← c.encode_length v.1]
    simp [c.decode_encode, d.decode_encode]

/-- A deliberately loose linear width for a bounded natural-number field.
The value itself is encoded in binary using Complexitylib's counter codec. -/
def fin (m : ℕ) : FixedWidthCodec (Fin m) where
  width := m
  encode v := Complexity.bitsOfLenLE m v.val
  decode bits := if h : bits.length = m ∧ Complexity.binValLE bits < m then
    some ⟨Complexity.binValLE bits, h.2⟩ else none
  encode_length v := Complexity.bitsOfLenLE_length _ _
  decode_encode v := by
    have value := Complexity.binValLE_bitsOfLenLE m v.val
      (v.isLt.trans (Nat.lt_two_pow_self))
    simp [value, v.isLt]

/-- Blank and nonblank tape symbols share one finite field. -/
def optionFin (m : ℕ) : FixedWidthCodec (Option (Fin m)) :=
  (fin (m + 1)).transport (finSuccEquiv m)

/-- A finite tape window, encoded one cell at a time. -/
def vector (c : FixedWidthCodec V) : (n : ℕ) → FixedWidthCodec (Fin n → V)
  | 0 => {
      width := 0
      encode := fun _ => []
      decode := fun bits => if bits = [] then some Fin.elim0 else none
      encode_length := fun _ => rfl
      decode_encode := fun v => by simp; funext i; exact Fin.elim0 i }
  | n + 1 => (c.prod (vector c n)).transport {
      toFun := fun p => Fin.cons p.1 p.2
      invFun := fun v => (v 0, Fin.tail v)
      left_inv := fun p => by simp
      right_inv := Fin.cons_self_tail }

@[simp] theorem vector_width (c : FixedWidthCodec V) (n : ℕ) :
    (c.vector n).width = c.width * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [vector, transport, prod, ih, Nat.mul_succ, Nat.add_comm]

end FixedWidthCodec
end ComplexityOfGenerators
