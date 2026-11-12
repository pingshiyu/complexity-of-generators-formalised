import ComplexityOfGenerators.SelfReducibility
import ComplexityOfGenerators.Proofs.ResourceGeneration
import Mathlib.Data.Nat.Log

/-!
# Exact recursive generators with the current paper's hypotheses

The label bound is data rather than a computational oracle. The inverse is
specified only on labels in that bound. Both generator components have bounds
on accepting runs, including when their target language is empty.
-/
namespace ComplexityOfGenerators

structure PaperExactRecursiveGenerators {α : Type} [Fintype α] {L : Language α}
    (R : SelfReduction L) where
  labelBound : ℕ → ℕ
  logCoefficient : ℕ
  logConstant : ℕ
  labelBound_log : ∀ n, labelBound n ≤ logCoefficient * Nat.log 2 (n + 1) + logConstant
  width_le : ∀ n x, x.length ≤ n → R.width x ≤ labelBound n
  base : UniformGenerators α
  baseTime : PolynomialBound
  base_language : ∀ n, base.layer n = R.bases n
  base_time : ∀ n, base.machine.AcceptingTimeBound (generatorData n) (baseTime n)
  inverse : Machine α α α
  inverseTime : PolynomialBound
  inverse_generator : ∀ n y w, y ∈ L → w.length ≤ labelBound n →
    inverse.IsGenerator { input := y, auxiliary := w, index := n }
  inverse_language : ∀ n y w, y ∈ L → w.length ≤ labelBound n →
    inverse.generatedLanguage { input := y, auxiliary := w, index := n } =
      R.inverseFibre n y w
  inverse_time : ∀ n y w, y ∈ L → w.length ≤ labelBound n →
    inverse.AcceptingTimeBound { input := y, auxiliary := w, index := n } (inverseTime n)

/-- The current paper's exact-recursive criterion. No trial budgets or
behaviour of inverse calls outside the bounded-label domain are assumed. -/
def PaperExactlyRecursivelyGenerable {α : Type} [Fintype α] (L : Language α) : Prop :=
  ∃ R : SelfReduction L, Nonempty (PolynomialSelfReduction R) ∧
    Nonempty (PaperExactRecursiveGenerators R)

end ComplexityOfGenerators
