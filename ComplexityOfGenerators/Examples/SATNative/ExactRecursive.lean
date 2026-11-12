import ComplexityOfGenerators.Examples.SATNative.PolynomialReduction
import ComplexityOfGenerators.Examples.SATNative.InverseNative
import ComplexityOfGenerators.Proofs.ExactRecursiveGeneration

/-! The concrete padded-CNF SAT construction has all semantic and native
computational fields needed by exact recursive generability. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF

/-- Padded CNF SAT is exactly recursively generable by the concrete native
base sampler and fresh-variable inverse construction. -/
theorem exactlyRecursivelyGenerable : ExactlyRecursivelyGenerable language :=
  ⟨selfReduction, ⟨polynomialSelfReduction⟩, ⟨InverseNative.recursiveGenerators⟩⟩

/-- The manuscript's concrete SAT construction yields a native polynomial
generator via the general exact-recursion theorem. -/
theorem language_mem_pg : language ∈ PG Symbol :=
  exactlyRecursivelyGenerable_mem_pg exactlyRecursivelyGenerable

end ComplexityOfGenerators.Examples.PaddedCNF
