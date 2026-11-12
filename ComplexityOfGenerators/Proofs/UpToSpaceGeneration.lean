import ComplexityOfGenerators.Proofs.UpToElementaryGenerators
import ComplexityOfGenerators.Simulation.FixedFallbackSpace
import ComplexityOfGenerators.Foundations.StationarySpace
import ComplexityOfGenerators.Foundations.LengthSlices

/-! Cumulative generation from deterministic space-bounded decision.  A finite
set of candidate words has a common terminating decision time, used only in
the semantic proof.  The machine and its space bound do not use that time. -/

namespace ComplexityOfGenerators

open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace UpToSpaceGeneration

variable {α : Type} [Fintype α] (D : Machine α Bool Unit)

theorem finite_time_bound (deterministic : D.Deterministic)
    (halts : ∀ word, D.Halts (decisionData word) []) (n : ℕ) :
    ∃ time, ∀ word : List α, word.length ≤ n → D.TimeBound (decisionData word) time := by
  classical
  have each (word : List α) : ∃ time, D.TimeBound (decisionData word) time := by
    obtain ⟨time, result, halted⟩ := halts word
    refine ⟨time, fun bits => ⟨result, ?_⟩⟩
    rw [D.deterministic_run deterministic _ bits []]
    exact halted
  choose clocks bounded using each
  obtain ⟨time, upper⟩ := ((finite_words_length_le α n).image clocks).bddAbove
  refine ⟨time, fun word length bits => ?_⟩
  exact D.haltsWithin_mono _ bits (upper ⟨word, length, rfl⟩) (bounded word bits)

variable [Nonempty α] (L : Language α)
    (deterministic : D.Deterministic) (halts : ∀ word, D.Halts (decisionData word) [])
    (language : ∀ word, D.Accepts (decisionData word) [] ↔ word ∈ L)
    (fallback : List α) (member : fallback ∈ L)
    (shortest : ∀ word ∈ L, fallback.length ≤ word.length)

omit [Fintype α] [Nonempty α] in
include deterministic language in
theorem nondeterministic_language (word : List α) :
    (∃ bits, D.Accepts (decisionData word) bits) ↔ word ∈ L := by
  constructor
  · rintro ⟨bits, accepted⟩
    exact (language word).mp ((D.deterministic_accepts deterministic _ bits []).mp accepted)
  · intro member
    exact ⟨[], (language word).mpr member⟩

def family : UpToGeneratorFamily α L where
  machine := fixedFallbackGenerator (finiteUpToWordSampler α) D fallback
  isGenerator := by
    intro n
    obtain ⟨time, bounded⟩ := finite_time_bound D deterministic halts n
    exact fixedFallback_isGenerator (finiteUpToWordSampler α) D fallback L n ((Fintype.card α + 2) * n) time
      (finiteUpToWordSampler_run α n)
      (fun word length => by rw [finiteUpToWordSampler_language]; exact length)
      bounded (nondeterministic_language D L deterministic language) member shortest
  layers := by
    intro n
    obtain ⟨time, bounded⟩ := finite_time_bound D deterministic halts n
    exact fixedFallback_support (finiteUpToWordSampler α) D fallback L n ((Fintype.card α + 2) * n) time
      (finiteUpToWordSampler_run α n)
      (fun word length => by rw [finiteUpToWordSampler_language]; exact length)
      bounded (nondeterministic_language D L deterministic language) member shortest

theorem family_spaceBound (space : ℕ → ℕ) (monotone : Monotone space)
    (bounded : ∀ word, D.SpaceBound (decisionData word) (space word.length)) (n : ℕ) :
    (family D L deterministic halts language fallback member shortest).machine.SpaceBound (generatorData n)
      (2 * fixedFallbackRadius n ((Fintype.card α + 2) * n) (space n) fallback.length + 1) := by
  apply fixedFallback_spaceBound (finiteUpToWordSampler α) D fallback deterministic n ((Fintype.card α + 2) * n) (space n)
    (finiteUpToWordSampler_run α n) (fun word _ => halts word)
  intro word length
  exact (bounded word).mono D (monotone length)

end UpToSpaceGeneration

/-- An arbitrary-resource fragment: a deterministic `s(n)`-space decider for a
nonempty language gives a genuine cumulative generator in `O(n+s(n))` space.
The constant depends on the finite alphabet and its shortest accepted word. -/
theorem upTo_generation_of_deterministic_space {α : Type} [Fintype α] [Nonempty α]
    (L : Language α) (D : Machine α Bool Unit) (deterministic : D.Deterministic)
    (halts : ∀ word, D.Halts (decisionData word) [])
    (language : ∀ word, D.Accepts (decisionData word) [] ↔ word ∈ L)
    (space : ℕ → ℕ) (monotone : Monotone space)
    (bounded : ∀ word, D.SpaceBound (decisionData word) (space word.length)) (nonempty : L.Nonempty) :
    ∃ G : UpToGeneratorFamily α L, ∃ constant : ℕ, 0 < constant ∧
      ∀ n, G.machine.SpaceBound (generatorData n) (constant * (n + space n + 1)) := by
  classical
  have lengths : ∃ n, ∃ word ∈ L, word.length = n := by
    obtain ⟨word, member⟩ := nonempty
    exact ⟨word.length, word, member, rfl⟩
  obtain ⟨fallback, member, length⟩ := Nat.find_spec lengths
  have shortest : ∀ word ∈ L, fallback.length ≤ word.length := by
    intro word wordMember
    rw [length]
    exact Nat.find_min' lengths ⟨word, wordMember, rfl⟩
  let G := UpToSpaceGeneration.family D L deterministic halts language fallback member shortest
  let constant := 40 * (Fintype.card α + fallback.length + 5) + 1
  refine ⟨G, constant, by unfold constant; omega, fun n => ?_⟩
  apply (UpToSpaceGeneration.family_spaceBound D L deterministic halts language fallback member shortest
    space monotone bounded n).mono G.machine
  unfold fixedFallbackRadius constant
  nlinarith

/-- Under the cumulative-generation proposition's hypothesis `s(n) ≥ n`, the
preceding deterministic construction has `O(s)` space overhead. The general
nondeterministic converse is separate. -/
theorem upTo_generation_of_linear_space {α : Type} [Fintype α] [Nonempty α]
    (L : Language α) (D : Machine α Bool Unit) (deterministic : D.Deterministic)
    (halts : ∀ word, D.Halts (decisionData word) [])
    (language : ∀ word, D.Accepts (decisionData word) [] ↔ word ∈ L)
    (space : ℕ → ℕ) (monotone : Monotone space) (positive : ∀ n, 0 < space n)
    (linear : ∀ n, n ≤ space n)
    (bounded : ∀ word, D.SpaceBound (decisionData word) (space word.length)) (nonempty : L.Nonempty) :
    ∃ G : UpToGeneratorFamily α L, ∃ constant : ℕ, 0 < constant ∧
      ∀ n, G.machine.SpaceBound (generatorData n) (constant * space n) := by
  obtain ⟨G, constant, positiveConstant, boundedG⟩ := upTo_generation_of_deterministic_space
    L D deterministic halts language space monotone bounded nonempty
  refine ⟨G, 3 * constant, by omega, fun n => (boundedG n).mono G.machine ?_⟩
  have size : n + space n + 1 ≤ 3 * space n := by have := linear n; have := positive n; omega
  nlinarith

theorem pspace_subset_pspacegUpTo {α : Type} [Fintype α] : PSPACE α ⊆ PSPACEGUpTo α := by
  classical
  intro L member
  have empty : (∅ : Language α) ∈ PSPACEGUpTo α := by
    refine ⟨emptyUpToFamily α, ⟨1, 0, by decide⟩, fun n => ?_⟩
    change (emptyGenerator α).SpaceBound (generatorData n) 1
    apply Machine.StationaryWork.spaceBound
    intro q input auxiliary index cell
    trivial
  have epsilon : ({[]} : Language α) ∈ PSPACEGUpTo α := by
    refine ⟨emptyWordUpToFamily α, ⟨1, 0, by decide⟩, fun n => ?_⟩
    change (wordEmitter ([] : List α)).SpaceBound (generatorData n) 1
    apply Machine.StationaryWork.spaceBound
    intro q input auxiliary index cell
    simp [wordEmitter]
  by_cases inhabited : Nonempty α
  · letI := inhabited
    by_cases nonempty : L.Nonempty
    · obtain ⟨D, bound, deterministic, halts, bounded, language⟩ := member
      obtain ⟨G, constant, _, boundedG⟩ := upTo_generation_of_deterministic_space
        L D deterministic halts language bound bound.monotone bounded nonempty
      let polynomial : Polynomial ℕ := Polynomial.C constant * (Polynomial.X + bound.asPolynomial + 1)
      refine ⟨G, PolynomialBound.ofPolynomial polynomial, fun n => (boundedG n).mono G.machine ?_⟩
      have upper := PolynomialBound.eval_le_ofPolynomial polynomial n
      simpa only [polynomial, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_add,
        Polynomial.eval_X, Polynomial.eval_one, PolynomialBound.asPolynomial_eval] using upper
    · simpa [Set.not_nonempty_iff_eq_empty.mp nonempty] using empty
  · letI : IsEmpty α := ⟨fun a => inhabited ⟨a⟩⟩
    have only (word : Word α) : word = [] := by
      cases word with | nil => rfl | cons letter _ => exact isEmptyElim letter
    by_cases contains : [] ∈ L
    · have language : L = {[]} := by ext word; rw [only word]; simp [contains]
      simpa [language] using epsilon
    · have language : L = ∅ := by ext word; rw [only word]; simp [contains]
      simpa [language] using empty

theorem pspacegUpTo_eq_pspace {α : Type} [Fintype α] : PSPACEGUpTo α = PSPACE α :=
  Set.Subset.antisymm pspacegUpTo_subset_pspace pspace_subset_pspacegUpTo

end
end ComplexityOfGenerators
