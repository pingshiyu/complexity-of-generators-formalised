import ComplexityOfGenerators.Simulation.OutputMatcherSpace
import ComplexityOfGenerators.Foundations.SpaceSearch
import ComplexityOfGenerators.Foundations.ResourceBounds
import ComplexityOfGenerators.Foundations.BoundedGeneration

/-!
# The polynomial-depth reachability reduction for Theorem 6.1

Membership in a polynomial-space generator's language is decided by midpoint
search with polynomial recursion depth and polynomial-size configuration
windows. All random-tape lengths, empty slices, and empty words are covered.

This retains an independent mathematical search specification. The machine
implementation in `PolynomialSpaceBase` uses the space-preserving native/library
translations and Complexitylib’s verified finite configuration search.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section

variable {α : Type} [Fintype α]

/-- The exponent of the streaming comparator's configuration count, expressed
as a polynomial in word length. Its index is also the word length. -/
def generatorSearchDepthPolynomial (M : Machine Unit Bool α) (space : PolynomialBound) :
    Polynomial ℕ :=
  Polynomial.C ((outputMatcher M).states + 1) + 2 * (Polynomial.X + 1) +
    (2 * space.asPolynomial + 1) +
    Polynomial.C (M.symbols + 1) * (2 * space.asPolynomial + 1)

def generatorSearchDepth (M : Machine Unit Bool α) (space : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (generatorSearchDepthPolynomial M space)

theorem generatorSearchDepth_bound (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) :
    (outputMatcher M).spaceConfigurationExponent ⟨word, [], word.length⟩ (space word.length) ≤
      generatorSearchDepth M space word.length := by
  have bound := PolynomialBound.eval_le_ofPolynomial (generatorSearchDepthPolynomial M space) word.length
  have evaluation : (generatorSearchDepthPolynomial M space).eval word.length =
      (outputMatcher M).spaceConfigurationExponent ⟨word, [], word.length⟩ (space word.length) := by
    simp only [generatorSearchDepthPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
      Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one,
      PolynomialBound.asPolynomial_eval, Machine.spaceConfigurationExponent, List.length_nil,
      outputMatcher]
    omega
  rw [evaluation] at bound
  exact bound

/-- The explicit midpoint search for a word in a native generator's output
slice. It tests output equality with a streaming comparator, not stored output. -/
def generatorSpaceSearch (M : Machine Unit Bool α) (space : PolynomialBound)
    (word : List α) : Bool :=
  (outputMatcher M).spaceSearch ⟨word, [], word.length⟩ (space word.length)
    (generatorSearchDepth M space word.length)

theorem generatorSpaceSearch_correct (M : Machine Unit Bool α) (space : PolynomialBound)
    (bounded : ∀ n, M.SpaceBound (generatorData n) (space n)) (word : List α) :
    generatorSpaceSearch M space word = true ↔ word ∈ M.generatedLanguage (generatorData word.length) := by
  have matcherSpace := outputMatcher_spaceBound M ⟨word, [], word.length⟩ (space word.length)
    (bounded word.length)
  rw [generatorSpaceSearch, matcherSpace.spaceSearch_correct (outputMatcher M) _
    (generatorSearchDepth_bound M space word)]
  simp only [outputMatcher_accepts_iff]
  constructor
  · rintro ⟨bits, produced⟩
    exact ⟨bits ++ [false], by simp, M.produces_append _ bits [false] word produced⟩
  · rintro ⟨bits, _, produced⟩
    exact ⟨bits, produced⟩

/-- Every polynomial-space generable language has the proved polynomial-depth
search specification, with the original generator as its uniform machine
parameter. This does not assert a native search implementation. -/
theorem pspaceg_has_polynomialDepth_search {L : Language α} (member : L ∈ PSPACEG α) :
    ∃ (G : GeneratorFamily α) (space : PolynomialBound),
      G.toUniformGenerators.language = L ∧
      G.toUniformGenerators.RunsInSpace space ∧
      ∀ word, generatorSpaceSearch G.machine space word = true ↔ word ∈ L := by
  obtain ⟨G, language, space, bounded⟩ := member
  refine ⟨G, space, language, bounded, ?_⟩
  intro word
  rw [generatorSpaceSearch_correct G.machine space bounded]
  change word ∈ G.toUniformGenerators.layer word.length ↔ word ∈ L
  rw [G.layer_eq_lengthSlice, language]
  exact ⟨fun member => member.1, fun member => ⟨member, rfl⟩⟩

end
end ComplexityOfGenerators
