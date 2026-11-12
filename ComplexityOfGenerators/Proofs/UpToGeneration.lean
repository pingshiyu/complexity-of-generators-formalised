import ComplexityOfGenerators.Proofs.ResourceGeneration
import ComplexityOfGenerators.Proofs.ResourceGenerationSpace

/-!
# Cumulative output slices and their native decision procedures

These definitions express the paper's up-to-size convention directly on one
uniform native machine.  In particular, the time condition bounds accepting
executions only: an empty slice need not exhaust an arbitrarily long finite
random tape within the same bound.

The results below establish the generator-to-decider directions of the
polynomial specialisations of Proposition 4.2.  They do not claim the arbitrary
`O(t)`/`O(s)` equalities: the existing single-work-tape time compiler has a
polynomial, rather than linear, overhead.
-/

namespace ComplexityOfGenerators

/-- All words of a language whose length is at most the index. -/
def upToSlice {α : Type} (L : Language α) (n : ℕ) : Language α :=
  {w | w ∈ L ∧ w.length ≤ n}

/-- The paper's up-to-size family, implemented by one actual native machine. -/
structure UpToGeneratorFamily (α : Type) [Fintype α] (L : Language α)
    extends UniformGenerators α where
  layers : ∀ n, toUniformGenerators.layer n = upToSlice L n

/-- Arbitrary accepting-time bounds on actual cumulative generators. -/
def GTIMEUpTo (α : Type) [Fintype α] (time : ℕ → ℕ) : LanguageClass α :=
  {L | ∃ G : UpToGeneratorFamily α L,
    ∀ n, G.machine.AcceptingTimeBound (generatorData n) (time n)}

/-- Arbitrary work-space bounds on every run of a cumulative generator. -/
def GSPACEUpTo (α : Type) [Fintype α] (space : ℕ → ℕ) : LanguageClass α :=
  {L | ∃ G : UpToGeneratorFamily α L, G.toUniformGenerators.RunsInSpace space}

/-- Languages with a cumulative-slice generator whose accepting runtime is
bounded by a uniform polynomial. -/
def PGUpTo (α : Type) [Fintype α] : LanguageClass α :=
  {L | ∃ G : UpToGeneratorFamily α L, G.toUniformGenerators.AcceptingPolynomialTime}

/-- Languages with cumulative-slice generators using uniformly polynomial
space on every run. -/
def PSPACEGUpTo (α : Type) [Fintype α] : LanguageClass α :=
  {L | ∃ G : UpToGeneratorFamily α L, G.toUniformGenerators.PolynomialSpace}

theorem mem_pgUpTo_iff_exists_polynomial {α : Type} [Fintype α] (L : Language α) :
    L ∈ PGUpTo α ↔ ∃ p : PolynomialBound, L ∈ GTIMEUpTo α p := by
  constructor
  · rintro ⟨G, p, bound⟩
    exact ⟨p, G, bound⟩
  · rintro ⟨p, G, bound⟩
    exact ⟨G, p, bound⟩

theorem mem_pspacegUpTo_iff_exists_polynomial {α : Type} [Fintype α] (L : Language α) :
    L ∈ PSPACEGUpTo α ↔ ∃ p : PolynomialBound, L ∈ GSPACEUpTo α p := by
  constructor
  · rintro ⟨G, p, bound⟩
    exact ⟨p, G, bound⟩
  · rintro ⟨p, G, bound⟩
    exact ⟨G, p, bound⟩

noncomputable section

variable {α : Type} [Fintype α]

/-- The time direction of the polynomial up-to-size characterisation uses an
actual native recognizer and the proved polynomial clock compiler. -/
theorem pgUpTo_subset_np : PGUpTo α ⊆ NP α := by
  rintro L ⟨G, bounded⟩
  apply mem_np_of_polynomial_layer_generation L G.toUniformGenerators ?_ bounded
  intro word
  rw [G.layers]
  simp [upToSlice]

/-- Cumulative slices have the same polynomial-space recognition construction
as exact slices.  The result uses actual visited-cell bounds, streaming output
comparison, and the proved native/library space translations. -/
theorem pspacegUpTo_subset_pspace : PSPACEGUpTo α ⊆ PSPACE α := by
  rintro L ⟨G, bounded⟩
  apply mem_pspace_of_polynomial_layer_generation L G.toUniformGenerators ?_ bounded
  intro word
  rw [G.layers]
  simp [upToSlice]

end
end ComplexityOfGenerators
