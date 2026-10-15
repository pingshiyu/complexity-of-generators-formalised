import ComplexityOfGenerators.Proofs.PolynomialSpaceStack
import ComplexityOfGenerators.Simulation.SavitchMachine.Execution

/-!
# Polynomial bounds for the concrete Savitch frame layout

The configuration-graph search already has a verified library-stack execution.
Here its invariant bounds the six physical frame columns used by the new
load/store/erase routines. This is a bound on that layout and its routines;
the full containment is assembled in `PolynomialSpaceBase`. The recursive
dispatcher is implemented in `SavitchMachine.Execution`.
-/

namespace ComplexityOfGenerators

open Simulation Complexity

noncomputable section

variable {α : Type} [Fintype α]

theorem generatorStackRun_frameSize (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) (steps : ℕ) :
    Sav.StkSize (generatorSearchDepth M space word.length)
      ((outputMatcher M).spaceCodeCodec ⟨word, [], word.length⟩ (space word.length)).width
      (generatorStackRun M space word steps).stk := by
  let matcher := outputMatcher M
  let data : InputData α Bool := ⟨word, [], word.length⟩
  let codec := matcher.spaceCodeCodec data (space word.length)
  let depth := generatorSearchDepth M space word.length
  let start := matcher.initialSpaceCode data (space word.length)
  have initialSize : Sav.StkSize depth codec.width (SavitchStack.initial codec depth start).stk := by
    simp [SavitchStack.initial, SavitchStack.root, Sav.StkSize, Sav.FrmSize, codec.encode_length]
  exact Sav.iterate_stkSize (matcher.spaceReachBase data (space word.length))
    (matcher.spaceAcceptBase data (space word.length)) (SavitchStack.zeroCode codec)
    (by simp only [SavitchStack.zeroCode_length]; exact Nat.le_refl _) steps _ initialSize

/-- Every live midpoint retains the configuration-code width exactly. -/
theorem generatorStackRun_midpointWidth (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) (steps : ℕ) :
    SavitchMachine.MidpointWidth
      ((outputMatcher M).spaceCodeCodec ⟨word, [], word.length⟩ (space word.length)).width
      (generatorStackRun M space word steps).stk := by
  let matcher := outputMatcher M
  let data : InputData α Bool := ⟨word, [], word.length⟩
  let codec := matcher.spaceCodeCodec data (space word.length)
  let depth := generatorSearchDepth M space word.length
  let start := matcher.initialSpaceCode data (space word.length)
  have initial : SavitchMachine.MidpointWidth codec.width
      (SavitchStack.initial codec depth start).stk := by
    simp [SavitchStack.initial, SavitchStack.root, SavitchMachine.MidpointWidth]
  exact SavitchMachine.iterate_midpointWidth (matcher.spaceReachBase data (space word.length))
    (matcher.spaceAcceptBase data (space word.length)) (SavitchStack.zeroCode codec)
    codec.width (SavitchStack.zeroCode_length codec) _ initial steps

/-- Every column of the concrete frame representation stays within the same
uniform polynomial used for the serialized library stack. -/
theorem generatorStackRun_column_length (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) (steps : ℕ) (j : Fin 6) :
    (SavitchMachine.Frames.column (generatorStackRun M space word steps).stk j).length ≤
      generatorStackSpace M space word.length := by
  have columns := SavitchMachine.Frames.column_bound (generatorStackRun_frameSize M space word steps) j
  have width := generatorSearchDepth_bound M space word
  rw [Machine.spaceCodeCodec_width] at columns
  have square : SavitchMachine.Frames.frameRadius (generatorSearchDepth M space word.length)
      ((outputMatcher M).spaceConfigurationExponent ⟨word, [], word.length⟩ (space word.length)) ≤
      44 * (generatorSearchDepth M space word.length + 1) ^ 2 := by
    unfold SavitchMachine.Frames.frameRadius
    nlinarith
  have polynomial := PolynomialBound.eval_le_ofPolynomial
    (44 * ((generatorSearchDepth M space).asPolynomial + 1) ^ 2) word.length
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, PolynomialBound.asPolynomial_eval, Polynomial.eval_one] at polynomial
  exact columns.trans (square.trans polynomial)

end
end ComplexityOfGenerators
