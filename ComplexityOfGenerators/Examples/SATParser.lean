import ComplexityOfGenerators.Examples.SATBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF

set_option backward.isDefEq.respectTransparency false

/-- Consume exactly the leading unary marks, leaving the first other symbol. -/
def readOnes : List Symbol → ℕ × List Symbol
  | .one :: rest => let result := readOnes rest; (result.1 + 1, result.2)
  | rest => (0, rest)

theorem readOnes_reconstruct (input : List Symbol) :
    List.replicate (readOnes input).1 .one ++ (readOnes input).2 = input := by
  induction input with
  | nil => rfl
  | cons s rest ih =>
    cases s <;> simp [readOnes, List.replicate_succ, ih]

theorem readOnes_marks_zeros (marks zeros : ℕ) :
    readOnes (List.replicate marks .one ++ List.replicate zeros .zero) =
      (marks, List.replicate zeros .zero) := by
  induction marks with
  | zero => cases zeros <;> rfl
  | succ marks ih => simp [List.replicate_succ, readOnes, ih]

theorem readOnes_header (marks : ℕ) (rest : List Symbol) :
    readOnes (List.replicate marks .one ++ .separator :: rest) =
      (marks, .separator :: rest) := by
  induction marks with
  | zero => rfl
  | succ marks ih => simp [List.replicate_succ, readOnes, ih]

def Literal.decode (M : ℕ) : List Symbol → Option Literal
  | .trueConstant :: rest =>
      if rest = List.replicate M .zero then some (.constant true) else none
  | .falseConstant :: rest =>
      if rest = List.replicate M .zero then some (.constant false) else none
  | .positive :: rest =>
      let result := readOnes rest
      if 0 < result.1 ∧ result.1 ≤ M ∧ result.2 = List.replicate (M - result.1) .zero
      then some (.var result.1 true) else none
  | .negative :: rest =>
      let result := readOnes rest
      if 0 < result.1 ∧ result.1 ≤ M ∧ result.2 = List.replicate (M - result.1) .zero
      then some (.var result.1 false) else none
  | _ => none

theorem Literal.decode_encode (M : ℕ) (lit : Literal) (valid : lit.valid M) :
    Literal.decode M (lit.encode M) = some lit := by
  cases lit with
  | constant b => cases b <;> simp [encode, decode]
  | var j sign =>
    cases sign <;> simp [encode, decode, readOnes_marks_zeros, valid.1, valid.2]

private theorem decode_variable_sound (M : ℕ) (sign : Bool) (input : List Symbol)
    (lit : Literal)
    (decoded : (let result := readOnes input
      if 0 < result.1 ∧ result.1 ≤ M ∧ result.2 = List.replicate (M - result.1) .zero
      then some (Literal.var result.1 sign) else none) = some lit) :
    lit.valid M ∧ lit.encode M = (if sign then Symbol.positive else Symbol.negative) :: input := by
  dsimp only at decoded
  split_ifs at decoded with good
  · have literal : lit = .var (readOnes input).1 sign := (Option.some.inj decoded).symm
    subst lit
    refine ⟨⟨good.1, good.2.1⟩, ?_⟩
    have reconstruct := readOnes_reconstruct input
    rw [good.2.2] at reconstruct
    simpa [Literal.encode] using congrArg
      ((if sign then Symbol.positive else Symbol.negative) :: ·) reconstruct

theorem Literal.decode_sound (M : ℕ) (input : List Symbol) (lit : Literal)
    (decoded : Literal.decode M input = some lit) :
    lit.valid M ∧ lit.encode M = input := by
  cases input with
  | nil => simp [decode] at decoded
  | cons s rest =>
    cases s with
    | trueConstant =>
      simp only [decode] at decoded
      split_ifs at decoded with good
      · have literal : lit = .constant true := (Option.some.inj decoded).symm
        subst lit
        exact ⟨trivial, by simp [encode, good]⟩
    | falseConstant =>
      simp only [decode] at decoded
      split_ifs at decoded with good
      · have literal : lit = .constant false := (Option.some.inj decoded).symm
        subst lit
        exact ⟨trivial, by simp [encode, good]⟩
    | positive => exact decode_variable_sound M true rest lit decoded
    | negative => exact decode_variable_sound M false rest lit decoded
    | zero | one | separator | openClause | closeClause => simp [decode] at decoded

end ComplexityOfGenerators.Examples.PaddedCNF
