import ComplexityOfGenerators.Examples.HAMPATHNative.PolynomialReduction
import ComplexityOfGenerators.Examples.HAMPATHNative.InverseNative
import ComplexityOfGenerators.Proofs.ExactRecursiveGeneration

namespace ComplexityOfGenerators.Examples.HAMPATH

theorem exactlyRecursivelyGenerable : ExactlyRecursivelyGenerable language :=
  ⟨selfReduction,⟨polynomialSelfReduction⟩,⟨Native.Inverse.recursiveGenerators⟩⟩

theorem language_mem_pg : language∈PG Symbol :=
  exactlyRecursivelyGenerable_mem_pg exactlyRecursivelyGenerable

end ComplexityOfGenerators.Examples.HAMPATH
