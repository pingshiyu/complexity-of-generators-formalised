import ComplexityOfGenerators.Proofs.PolynomialSpaceStack
import ComplexityOfGenerators.Foundations.SpaceCodeFields

/-! The existing Savitch stack polynomial also bounds the configuration-test
routines. No larger space class or additional complexity assumption is needed
for their unary coordinate decoders, affine offsets, or tape-window scans. -/

namespace ComplexityOfGenerators

open Simulation Machine
noncomputable section
variable {α : Type} [Fintype α]

/-- A common linear allowance inside the already chosen quadratic bound. -/
theorem generatorStackSpace_linear (M : Machine Unit Bool α) (space : PolynomialBound) (n : ℕ) :
    2 * generatorSearchDepth M space n + 3 ≤ generatorStackSpace M space n := by
  have bound := PolynomialBound.eval_le_ofPolynomial
    (44 * ((generatorSearchDepth M space).asPolynomial + 1) ^ 2) n
  simp only [Polynomial.eval_mul, Polynomial.eval_ofNat, Polynomial.eval_pow,
    Polynomial.eval_add, PolynomialBound.asPolynomial_eval, Polynomial.eval_one] at bound
  change _ ≤ PolynomialBound.ofPolynomial _ n
  nlinarith

/-- Every temporary unary field decoder, including its doubled accumulator,
fits the existing generator stack bound. -/
theorem generator_header_decoder_room (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) (field : HeaderField) :
    2 * field.width (outputMatcher M).states word.length (space word.length) + 1 ≤
      generatorStackSpace M space word.length := by
  have width := (outputMatcher M).header_width_le_exponent word (space word.length) field
  have depth := generatorSearchDepth_bound M space word
  have room := generatorStackSpace_linear M space word.length
  omega

/-- Locating a field requires only a polynomial unary prefix counter. -/
theorem generator_header_offset_room (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) (field : HeaderField) :
    field.offset (outputMatcher M).states word.length ≤ generatorStackSpace M space word.length := by
  have offset := (outputMatcher M).header_offset_le_exponent word (space word.length) field
  have depth := generatorSearchDepth_bound M space word
  have room := generatorStackSpace_linear M space word.length
  omega

/-- The preserved input, polynomial ruler and full encoded tape window fit
individually; the radius also covers the ruler's transient construction. -/
theorem generator_base_storage_room (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) :
    word.length + space word.length + 1 ≤ generatorStackSpace M space word.length ∧
    2 * space word.length + 1 ≤ generatorStackSpace M space word.length ∧
    ((outputMatcher M).symbols + 1) * (2 * space word.length + 1) ≤
      generatorStackSpace M space word.length ∧
    (outputMatcher M).states + 2 * word.length + 2 * space word.length + 4 ≤
      generatorStackSpace M space word.length := by
  have depth := generatorSearchDepth_bound M space word
  have room := generatorStackSpace_linear M space word.length
  simp only [Machine.spaceConfigurationExponent, List.length_nil] at depth
  omega

end
end ComplexityOfGenerators
