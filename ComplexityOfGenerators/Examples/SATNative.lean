import ComplexityOfGenerators.Examples.SATNative.SyntaxComputability
import ComplexityOfGenerators.Examples.SATNative.CertificateCheck
import ComplexityOfGenerators.Examples.SATNative.VerifierMachine
import ComplexityOfGenerators.Examples.SATNative.BaseSampler
import ComplexityOfGenerators.Examples.SATNative.PolynomialReduction
import ComplexityOfGenerators.Examples.SATNative.ExactRecursive

/-!
# Concrete native machinery for padded CNF

`NativeParser.syntax_computable` is a genuine polynomial word function: its
finite stack controller parses the capacity/active-count header, every padded
literal record, and the complete nonempty-clause grammar. It agrees with the
checked functional decoder on all words, and its proof includes input loading,
primitive operation costs, finite-control compilation and native machine time.

`NativeAssignment` implements descending certificate-index lookup, evaluates
individual decoded literals, and checks binary certificate syntax and length.
`NativeEvaluation.NativeVerifier.machine` is the actual deterministic native
certificate verifier, with polynomial time and exact certificate-set
correctness on every pair of words. Its false cases natively reject.
These are implementation lemmas, not assumed-machine interfaces.

`BaseSampler.baseFamily` is a native polynomial generator for every
constant-formula base at each length. Its four-coin symbol proposals cover all
encoded words; the native verifier checks the empty certificate, and failures
use the implemented productive-length default. Its exact base support and
polynomial trial bounds are proved, including the empty base lengths.

`polynomialSelfReduction` assembles the completed native verifier, rank,
width and checked substitution transducer. Substitution agrees with the
manuscript's total `wordReduce` function on all word/label pairs, including
malformed inputs and rank-zero empty-label calls; its primitive time and
native compiled time are polynomial.

`InverseNative.recursiveGenerators` completes the native exact-recursion
instance. The inverse caps oversized inputs, checks exact target length and
labels, and samples fresh-variable replacement masks with exact fibre support
and uniform polynomial trial bounds. `exactlyRecursivelyGenerable` and
`language_mem_pg` assemble the concrete SAT instance and its polynomial
generability consequence.
-/
