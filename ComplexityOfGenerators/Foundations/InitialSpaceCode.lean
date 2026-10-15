import ComplexityOfGenerators.Foundations.SpaceCodeBits

/-! The initial configuration code, field by field. All read-only heads are
zero; the work-head coordinate is the offset of the origin in `[-s,s]`; every
work symbol is blank. This formula is the specification of the native input
initializer. -/

namespace ComplexityOfGenerators.FixedWidthCodec

open Complexity

theorem optionFin_encode_none (symbols : ℕ) :
    (optionFin symbols).encode none = List.replicate (symbols + 1) false := by
  simp [optionFin, transport, fin, bitsOfLenLE_zero]

theorem vector_encode_zero {V : Type} (c : FixedWidthCodec V) (v : V)
    (zero : c.encode v = List.replicate c.width false) (n : ℕ) :
    (c.vector n).encode (fun _ => v) = List.replicate (c.width * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
      change c.encode v ++ (c.vector n).encode (fun _ => v) = _
      rw [zero, ih, ← List.replicate_add]
      congr 1
      simp [Nat.mul_succ, Nat.add_comm]

theorem vector_encode_blank (symbols cells : ℕ) :
    ((optionFin symbols).vector cells).encode (fun _ => none) =
      List.replicate ((symbols + 1) * cells) false := by
  exact vector_encode_zero (optionFin symbols) none (optionFin_encode_none symbols) cells

end ComplexityOfGenerators.FixedWidthCodec

namespace ComplexityOfGenerators.Machine

open FixedWidthCodec Complexity
set_option backward.isDefEq.respectTransparency false
variable {I A O : Type} (M : Machine I A O)

/-- The initializer can construct this list from the input-length and space
rulers. Its only nonzero variable coordinate is the work-head offset `s`. -/
theorem initialSpaceCode_bits (data : InputData I A) (s : ℕ) :
    (M.spaceCodeCodec data s).encode (M.initialSpaceCode data s) =
      bitsOfLenLE M.states M.initial.val ++
        List.replicate (data.input.length + 1 + (data.auxiliary.length + 1) + (data.index + 1)) false ++
        bitsOfLenLE (2 * s + 1) s ++
        List.replicate ((M.symbols + 1) * (2 * s + 1)) false := by
  simp only [initialSpaceCode, spaceCodeEquiv, Equiv.coe_fn_symm_mk, boundedInitialView,
    DecisionView.encode, decisionView, initialConfiguration, spaceCodeCodec, prod, fin]
  simp [vector_encode_blank, bitsOfLenLE_zero, List.replicate_add, List.append_assoc]

/-- The exact initialization formula for the output-matching recognizer. -/
theorem initialSpaceCode_bits_matching (input : List I) (s : ℕ) :
    (M.spaceCodeCodec ⟨input, [], input.length⟩ s).encode
        (M.initialSpaceCode ⟨input, [], input.length⟩ s) =
      bitsOfLenLE M.states M.initial.val ++ List.replicate (2 * input.length + 3) false ++
        bitsOfLenLE (2 * s + 1) s ++ List.replicate ((M.symbols + 1) * (2 * s + 1)) false := by
  simpa only [List.length_nil, show input.length + 1 + (0 + 1) + (input.length + 1) =
    2 * input.length + 3 by omega] using M.initialSpaceCode_bits ⟨input, [], input.length⟩ s

end ComplexityOfGenerators.Machine
