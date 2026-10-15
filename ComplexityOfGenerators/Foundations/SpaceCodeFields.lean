import ComplexityOfGenerators.Foundations.SpaceCodeBits
import ComplexityOfGenerators.Foundations.FixedWidthCodecValidity

/-! The fields inspected by the configuration-graph base program. On matcher
inputs the auxiliary tape is empty and both other read-only bounds are the
word length. Each header offset is affine in that length. -/

namespace ComplexityOfGenerators

set_option backward.isDefEq.respectTransparency false
namespace FixedWidthCodec

variable {V W : Type}

theorem prod_decode_iff (c : FixedWidthCodec V) (d : FixedWidthCodec W)
    (bits : List Bool) (v : V) (w : W) :
    (c.prod d).decode bits = some (v, w) ↔
      c.decode (bits.take c.width) = some v ∧ d.decode (bits.drop c.width) = some w := by
  cases a : c.decode (bits.take c.width) <;> cases b : d.decode (bits.drop c.width) <;>
    simp [prod, a, b]

end FixedWidthCodec

namespace Machine

inductive HeaderField | state | input | auxiliary | index | work
  deriving DecidableEq, Fintype

namespace HeaderField

/-- Widths are deliberately linear, as in `spaceCodeCodec`. -/
def width (states n s : ℕ) : HeaderField → ℕ
  | .state => states
  | .input | .index => n + 1
  | .auxiliary => 1
  | .work => 2 * s + 1

/-- The coefficient of the input length in the field offset. -/
def coefficient : HeaderField → ℕ
  | .state | .input => 0
  | .auxiliary | .index => 1
  | .work => 2

/-- The constant part of the field offset. -/
def constant (states : ℕ) : HeaderField → ℕ
  | .state => 0
  | .input => states
  | .auxiliary => states + 1
  | .index => states + 2
  | .work => states + 3

def offset (states n : ℕ) (field : HeaderField) : ℕ :=
  field.coefficient * n + field.constant states

def bits (states n s : ℕ) (field : HeaderField) (code : List Bool) : List Bool :=
  (code.drop (field.offset states n)).take (field.width states n s)

end HeaderField

variable {I A O : Type} (M : Machine I A O)

/-- The typed value of each header coordinate. -/
def spaceCodeHeader (word : List I) (s : ℕ)
    (code : M.SpaceCode (⟨word, [], word.length⟩ : InputData I A) s) :
    (field : HeaderField) → Fin (field.width M.states word.length s)
  | .state => code.1
  | .input => code.2.1
  | .auxiliary => code.2.2.1
  | .index => code.2.2.2.1
  | .work => code.2.2.2.2.1

/-- Exact decomposition of the configuration decoder into five header tests
and the work-window test. This equivalence includes all malformed bitstrings. -/
theorem spaceCodeCodec_decode_fields (word : List I) (s : ℕ) (bits : List Bool)
    (code : M.SpaceCode (⟨word, [], word.length⟩ : InputData I A) s) :
    (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode bits = some code ↔
      (∀ field : HeaderField,
        (FixedWidthCodec.fin (field.width M.states word.length s)).decode
          (field.bits M.states word.length s bits) = some (M.spaceCodeHeader word s code field)) ∧
      ((FixedWidthCodec.optionFin M.symbols).vector (2 * s + 1)).decode
        (bits.drop (M.states + 2 * word.length + 2 * s + 4)) = some code.2.2.2.2.2 := by
  rcases code with ⟨state, input, auxiliary, index, work, cells⟩
  simp only [spaceCodeCodec, FixedWidthCodec.prod_decode_iff]
  have allFields (p : HeaderField → Prop) : (∀ f, p f) ↔
      p .state ∧ p .input ∧ p .auxiliary ∧ p .index ∧ p .work := by
    constructor
    · intro h; exact ⟨h _, h _, h _, h _, h _⟩
    · rintro ⟨hs, hi, ha, hx, hw⟩ f; cases f <;> assumption
  rw [allFields]
  simp only [spaceCodeHeader, HeaderField.bits, HeaderField.offset, HeaderField.coefficient,
    HeaderField.constant, HeaderField.width, Nat.zero_mul, Nat.zero_add, Nat.one_mul,
    FixedWidthCodec.fin, List.length_nil, List.drop_zero, List.drop_drop]
  have offsetInput : M.states + (word.length + 1) = word.length + (M.states + 1) := by omega
  have offsetIndex : M.states + (word.length + 1) + 1 = word.length + (M.states + 2) := by omega
  have offsetWork : M.states + (word.length + 1) + 1 + (word.length + 1) =
      2 * word.length + (M.states + 3) := by omega
  have offsetCells : M.states + (word.length + 1) + 1 + (word.length + 1) + (2 * s + 1) =
      M.states + 2 * word.length + 2 * s + 4 := by omega
  rw [offsetCells, offsetWork, offsetIndex, offsetInput]
  tauto

/-- A successful whole-code decode certifies each coordinate read by the
native offset-and-field parser. -/
theorem spaceCodeCodec_decode_header (word : List I) (s : ℕ) (bits : List Bool)
    (code : M.SpaceCode (⟨word, [], word.length⟩ : InputData I A) s)
    (decoded : (M.spaceCodeCodec ⟨word, [], word.length⟩ s).decode bits = some code)
    (field : HeaderField) :
    (FixedWidthCodec.fin (field.width M.states word.length s)).decode
      (field.bits M.states word.length s bits) = some (M.spaceCodeHeader word s code field) :=
  ((M.spaceCodeCodec_decode_fields word s bits code).mp decoded).1 field

theorem header_width_le_exponent (word : List I) (s : ℕ) (field : HeaderField) :
    field.width M.states word.length s ≤ M.spaceConfigurationExponent ⟨word, [], word.length⟩ s := by
  cases field <;> simp only [HeaderField.width, spaceConfigurationExponent, List.length_nil] <;> omega

theorem header_offset_le_exponent (word : List I) (s : ℕ) (field : HeaderField) :
    field.offset M.states word.length ≤ M.spaceConfigurationExponent ⟨word, [], word.length⟩ s := by
  cases field <;> simp only [HeaderField.offset, HeaderField.coefficient, HeaderField.constant,
    spaceConfigurationExponent, List.length_nil] <;> omega

end Machine
end ComplexityOfGenerators
