import ComplexityOfGenerators.Examples.SATBaseChoices
import ComplexityOfGenerators.Examples.SATBaseDefaultNative
import ComplexityOfGenerators.Examples.SATComputability
import ComplexityOfGenerators.Examples.SATNative
import ComplexityOfGenerators.Examples.HAMPATHFiniteChoices
import ComplexityOfGenerators.Examples.HAMPATHBaseNative
import ComplexityOfGenerators.Examples.HAMPATHNative

/-!
# Concrete SAT and HAMPATH exact-recursive constructions

The concrete padded-CNF and loop-free directed adjacency-matrix encodings have
checked parsers, codec laws, all-word self-reductions, rank/label bounds,
ancestors, base characterisations and exact inverse fibres. HAMPATH certificates
encode the next vertex in binary; loop-freeness excludes self-loops only.

Both constructions include actual native polynomial verifiers, rank/width and
forward-reduction machines, full-support base families and uniform inverse
generators. `PaddedCNF.exactlyRecursivelyGenerable` and
`HAMPATH.exactlyRecursivelyGenerable` package these machines, and their
`language_mem_pg` theorems apply the general exact-recursive generation proof.
-/
