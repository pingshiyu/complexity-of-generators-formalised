# Complexity of generators, formalised

Lean 4 formalisation of *Complexity Theory of Randomised Testing*,
using the supplied [paper](complexity-of-generators-formalisation.pdf).

**Status:** all five results labelled “Theorem” have faithful declarations and
concrete definitions. **Theorem 3.1 (`RE α = GEN α`) is completely proved** in
the retained finite-control machine model, for every finite alphabet. The native
`RE` class is also proved equivalent to Mathlib's recursively enumerable word
predicates. The construction reuses Mathlib's verified recursive-program and
Turing-machine compilers, with proved native input, output and random-tape adapters.

**Theorem 5.1 is also completely proved:** collision-resistant hashes imply
`PG Bool ⊂ NP Bool` and `¬ P Bool ⊆ PG Bool`. The proof retains the native
machine model and the existing cryptographic assumption, including a concrete
polynomial-time collision decider and the generator-to-collision-finder reduction.

**Theorem 7.1 is completely proved**, using native transcript verification and
sampler/recoverer composition with polynomial bounds.

**Theorem 7.2 is completely proved:** `NP ≠ coNP` implies that `PG` is not closed
under complement; independently, collision-resistant hashes imply that `PG` is
not closed under intersection. Both proofs use native machines and verified
polynomial bounds.

**Theorem 6.1 is completely proved:** `PSPACEG α = PSPACE α` for every finite
alphabet. The forward direction implements the paper's Savitch configuration-graph
search in the retained native model; the reverse direction implements its cyclic
generator construction. Both use actual visited-cell space bounds. All five
main theorems and their supporting lemmas have complete proofs, with no `sorry`
or custom axioms.

**Theorem 7.1 uses two user-approved corrections to the certificate definitions:**
certified instances may be empty words, and every sampled certificate must
certify an instance of the requested length. Certificates remain positive strings.
[EmptyWordGeneration.lean](ComplexityOfGenerators/Proofs/EmptyWordGeneration.lean)
proves why the original coverage condition needs correction: `{ε} ∈ PG`, but
`LiteralCertificateCoverage` cannot cover its size-zero slice. The counterexample
concerns that historical condition, not the corrected `HasCertificateScheme`.
The completed proof uses exactly the corrected `HasCertificateScheme` definition.

## Build

Lean and Mathlib are pinned to **v4.34.0**. Direct dependencies are
[Mathlib](https://github.com/leanprover-community/mathlib4),
[Complexitylib](https://github.com/SamuelSchlesinger/complexitylib) at
`d51bfbd39bea4d8a4a3282d4d4ddbb33709ea467`, and
[VCVio](https://github.com/Verified-zkEVM/VCVio) at
`9146f78c4f1bc2c9d8d92da686e9e375315ae5e7`. Transitive dependencies are pinned in
`lake-manifest.json`; no additional small project is imported directly.
With the usual Lean/Elan installation:

```sh
lake update --keep-toolchain
lake exe cache get
lake build
lake env lean scripts/AuditFoundations.lean
```

Import `ComplexityOfGenerators` to obtain the entire development. No local
unfinished-proof warning is expected. Upstream VCVio emits deprecation warnings. The first build compiles the imported
Complexitylib and VCVio modules that are not covered by Mathlib's cache.

The root Lake post-update hook applies a small, verbatim upstream proof
compatibility backport to Complexitylib. It changes four cast proofs and no
statements or definitions; see [patches/README.md](patches/README.md). Lake's
warning that Complexitylib has local changes refers to this recorded backport.

Import `ComplexityOfGenerators.Foundations` to use the supporting development
without importing the main theorem statements. The audit traverses the axiom
dependencies of every local declaration, including the imported proofs they use
and all five main theorems. No declaration is excluded.
It rejects `sorryAx`, custom axioms and unchecked evaluation
axioms; only `propext`, `Classical.choice` and `Quot.sound` are allowed.

## Supporting machinery

| File | Definitions and proved results | Use in the paper |
| --- | --- | --- |
| [Classical.lean](ComplexityOfGenerators/Foundations/Classical.lean) | Direct aliases of Complexitylib's `P`, `NP`, `coNP`, `PSPACE`, `NPSPACE`, `L`, `NL`, time/space classes, `FP`, Karp reductions and completeness. | Classical complexity terminology throughout. |
| [BasicTheorems.lean](ComplexityOfGenerators/Foundations/BasicTheorems.lean) | Imported proofs of `P ⊆ NP`, `P ⊆ PSPACE`, complement closure of `P`, time-to-space containment, `NL ⊆ P`, Cook–Levin, UNSAT coNP-completeness, `UNSAT ∈ NP ↔ NP = coNP`, and `PSPACE = NPSPACE`. | Theorems 5.1, 6.1 and 7.2. |
| [Computability.lean](ComplexityOfGenerators/Foundations/Computability.lean) | Mathlib encodings, partial-recursive enumerability, computable predicates and many-one reductions; imported proofs of Post's theorem and the halting problem. Mathlib's polynomial-time TM interface is exposed too. | Computability foundations for Theorem 3.1. |
| [ResourceBounds.lean](ComplexityOfGenerators/Foundations/ResourceBounds.lean) | Positive polynomial bounds, conversion to Mathlib polynomials, domination of every natural-coefficient polynomial, and bounds for addition, multiplication and composition. | Resource accounting for verifiers, samplers, recovery and reductions. |
| [SpaceBounds.lean](ComplexityOfGenerators/Foundations/SpaceBounds.lean) | Visited cells form an integer interval containing the origin and head; unvisited cells are blank. Space bounds control head coordinates and tape support. A native time bound `t` implies space at most `t+1`, including the terminal successor. | Finite configuration windows for Theorem 6.1. |
| [SpaceConfigurations.lean](ComplexityOfGenerators/Foundations/SpaceConfigurations.lean) | Faithful finite encoding of bounded decision configurations, exact code count and an exponential upper bound, plus correspondence of native transitions after erasing unobservable histories. Includes terminal successor configurations. | Configuration graphs for Theorem 6.1; this does not yet compile graph search into a native machine. |
| [Cryptography.lean](ComplexityOfGenerators/Foundations/Cryptography.lean) | Collision language, pigeonhole collision existence at every parameter, nonempty slices, injective pair codec, and a proved equivalence of the paper's assumption with VCVio's `SecurityGame.secureAgainst` and `negligible`. | Collision-resistance assumptions in Theorems 5.1 and 7.2. |
| [Probability.lean](ComplexityOfGenerators/Foundations/Probability.lean) | Fair-coin probability measure, cylinder mass `2⁻ᵏ`, and measurability of acceptance and collision-success events. | The probability semantics of generators and attackers. |
| [ModelBridge.lean](ComplexityOfGenerators/Foundations/ModelBridge.lean) | Explicit comparison interfaces and proved conditional transport of Savitch and the complement-nonclosure argument. | Records which generator-specific simulations remain to be constructed. |

The VCVio equivalence preserves unkeyed hashing and uniform polynomial-time
attackers, and proves both directions of the exact eventual/infinite-size
quantifiers. It does not add keyed hashing, nonuniform circuits or a new security
assumption. VCVio's imported game-reduction and polynomial-loss lemmas are then
available for subsequent cryptographic reductions.

### Proof components

The proof development contains these checked components:

| File | Completed proof components |
| --- | --- |
| [RandomTape.lean](ComplexityOfGenerators/Foundations/RandomTape.lean) | Successful outputs survive every extension of the random tape; deterministic runs ignore randomness; arbitrary-configuration execution composes with the original evaluator. |
| [BoundedGeneration.lean](ComplexityOfGenerators/Foundations/BoundedGeneration.lean) | `P ⊆ NP` in the original model; every generated word has an exact full-budget seed witness, including outputs originally witnessed by tapes longer than the budget; family layers equal language length slices. |
| [PostCore.lean](ComplexityOfGenerators/Simulation/PostCore.lean) | Concrete finite instruction-table simulator for Mathlib's Post machines; each source move/write costs one native transition; both directions of halting equivalence and absence of spurious output. |
| [PostMachine.lean](ComplexityOfGenerators/Simulation/PostMachine.lean) | Loads a genuine input from an initially blank work tape in `2n + 4` transitions; proves the compiled machine deterministic and its acceptance equivalent to definedness of source evaluation. |
| [FiniteSupport.lean](ComplexityOfGenerators/Simulation/FiniteSupport.lean), [StackMachine.lean](ComplexityOfGenerators/Simulation/StackMachine.lean), [RecursivePrograms.lean](ComplexityOfGenerators/Simulation/RecursivePrograms.lean) | Restricts finitely supported library programs to finite control and composes Mathlib's TM2, TM1, Post and partial-recursive-program simulations. Partial-recursive halting predicates have native recognizers on an explicitly stated encoding. |
| [BlockLoader.lean](ComplexityOfGenerators/Simulation/BlockLoader.lean), [BlockBootstrap.lean](ComplexityOfGenerators/Simulation/BlockBootstrap.lean), [BlockRecognizer.lean](ComplexityOfGenerators/Simulation/BlockRecognizer.lean) | A concrete finite-control loader for fixed per-letter encodings, with complete operational proofs in `BlockLoading` and `BlockStages`. Loading and rewinding take exactly `2 * encodedLength + 2 * inputLength + 5` transitions. |
| [WordCode.lean](ComplexityOfGenerators/Simulation/WordCode.lean), [WordInput.lean](ComplexityOfGenerators/Simulation/WordInput.lean) | An actual library recursive program computes the standard word code; the native adapter reads ordinary source words and supplies the required stack encoding. Partial-recursive word predicates now have native recognizers on their original alphabet. |
| [WordOutput.lean](ComplexityOfGenerators/Simulation/WordOutput.lean), [RecursiveResult.lean](ComplexityOfGenerators/Simulation/RecursiveResult.lean) | An actual recursive program decodes a computed scalar word into reversed symbol codes. Mathlib's stack and Post simulations preserve the final main-stack projection needed to emit the original word. |
| [OutputMachine.lean](ComplexityOfGenerators/Simulation/OutputMachine.lean), [OutputCorrectness.lean](ComplexityOfGenerators/Simulation/OutputCorrectness.lean) | A concrete finite dictionary decoder emits the computed word in the retained native model. `OutputEncoding` and `OutputScanning` prove the binary encoding and every scanning step, including empty words and zero-valued letter codes. |
| [RoutineComposition.lean](ComplexityOfGenerators/Simulation/RoutineComposition.lean), [PostOutput.lean](ComplexityOfGenerators/Simulation/PostOutput.lean) | Concrete finite-control composition preserves the work tape and takes one step to transfer control. `PostContinuation` and `PostOutput` prove that a terminating Post simulation with the specified final main stack emits exactly its computed word. |
| [FiniteEvaluator.lean](ComplexityOfGenerators/Simulation/FiniteEvaluator.lean), [ComputableEvaluator.lean](ComplexityOfGenerators/Simulation/ComputableEvaluator.lean) | A finite list representation of work-tape writes and visited cells; exact correspondence with the native evaluator at every clock, including rejection and exhaustion; primitive recursiveness of bounded evaluation, using Mathlib encodings and list recursion. |
| [PrimitiveOperations.lean](ComplexityOfGenerators/Simulation/PrimitiveOperations.lean), [InstructionEncoding.lean](ComplexityOfGenerators/Simulation/InstructionEncoding.lean), [EvaluatorEncoding.lean](ComplexityOfGenerators/Simulation/EvaluatorEncoding.lean) | Primitive-recursive integer head movement, instruction case analysis, input data and configuration constructors and projections. The finite transition table is proved primitive recursive, rather than assumed computable. |
| [SeedEnumeration.lean](ComplexityOfGenerators/Proofs/SeedEnumeration.lean) | Dovetailed search over nonempty seeds and clocks; its domain is exactly native output support, even for machines that loop on some seeds. Compilation gives a concrete native recognizer on explicitly encoded words. |
| [RecognitionSearch.lean](ComplexityOfGenerators/Proofs/RecognitionSearch.lean) | Clock search has exactly native acceptance as its domain. Languages in the local `RE` and `GEN` classes give Mathlib recursively enumerable predicates. |
| [GenerabilityContainment.lean](ComplexityOfGenerators/Proofs/GenerabilityContainment.lean) | Complete proofs of `GEN α ⊆ RE α` for every finite alphabet, and of equivalence between native `RE` and Mathlib's recursively enumerable word predicates. No encoded-input qualification remains. |
| [ClockedSampling.lean](ComplexityOfGenerators/Proofs/ClockedSampling.lean) | A primitive-recursive finite-tape sampling algorithm with explicit exhaustion, bounded native recognition and fallback. Proves exact output support, preservation under seed extension, measurable acceptance and probability-one completion of its two geometric counters. The native construction uses binary samples with the same full-support guarantee. |
| [ClockProgram.lean](ComplexityOfGenerators/Proofs/ClockProgram.lean) | An actual total library recursive program performs bounded native recognition with fallback and returns reversed symbol codes. Its complete value specification proves soundness and coverage of every recognized word. |
| [BinarySampling.lean](ComplexityOfGenerators/Proofs/BinarySampling.lean) | Canonical binary number sampling has an explicit seed for every natural number, preserves samples under seed extension, and splits successful seeds into their consumed prefix and remainder. The measurable event of completing both successive samples has probability one. |
| [BinaryInput.lean](ComplexityOfGenerators/Simulation/BinaryInput.lean), [BinaryInputCorrectness.lean](ComplexityOfGenerators/Proofs/BinaryInputCorrectness.lean) | A concrete native transition table samples and writes the clock/candidate stack directly. `BinaryInputSteps`, `BinaryInputDigits`, `BinaryInputNumber`, `BinaryInputPair`, `BinaryInputBootstrap` and `BinaryInputRewind` prove reads, exhaustion, writes, number and pair encoding, blank-tape bootstrap and rewinding. Every chosen clock/candidate pair has a proved execution into the actual initial Post configuration. |
| [BinaryInputExhaustion.lean](ComplexityOfGenerators/Proofs/BinaryInputExhaustion.lean) | Every finite tape either contains two complete samples or causes the actual native sampler to exhaust, including tapes ending between a continuation flag and its digit. |
| [RoutineExecution.lean](ComplexityOfGenerators/Simulation/RoutineExecution.lean), [BinaryInputComposition.lean](ComplexityOfGenerators/Proofs/BinaryInputComposition.lean) | Sequential composition preserves live and exhausted executions. The combined sampler, Post computation and output routine produces the computed word from an actual blank initial tape, even when the Post program halts immediately. |
| [FiniteResults.lean](ComplexityOfGenerators/Simulation/FiniteResults.lean), [FiniteRecursiveResults.lean](ComplexityOfGenerators/Simulation/FiniteRecursiveResults.lean) | Restriction to finite support preserves the final tape and head position. The composed library compiler retains the returned word on its final main stack. |
| [RecursiveGenerator.lean](ComplexityOfGenerators/Proofs/RecursiveGenerator.lean) | A concrete native generator for any total two-argument recursive word program: halting on every finite tape, no explicit rejection, almost-sure acceptance, and generated language exactly equal to the program's range. |
| [RecognizabilityContainment.lean](ComplexityOfGenerators/Proofs/RecognizabilityContainment.lean) | Complete proof of `RE α ⊆ GEN α`, including the empty language and empty word, with no added assumption on the finite alphabet or recognizer. Together with the reverse containment, proves the main Theorem 3.1. |
| [GeneratorSupport.lean](ComplexityOfGenerators/Proofs/GeneratorSupport.lean) | Positive acceptance measure for nonempty output support; probability one iff a generator's language is nonempty; accepted-prefix events equal the paper's minimal-prefix events. |
| [GeneratorCriteria.lean](ComplexityOfGenerators/Proofs/GeneratorCriteria.lean) | Shared criteria deriving the generator probability condition from full trials and constructing a `PG` witness from exact length slices and separate polynomial seed/time bounds. Used by composition, fallback generation and deterministic replay. |
| [ElementaryGenerators.lean](ComplexityOfGenerators/Proofs/ElementaryGenerators.lean) | Concrete empty and singleton generators, including the empty word; a concrete looping recognizer for the empty language. |
| [GeometricSampling.lean](ComplexityOfGenerators/Proofs/GeometricSampling.lean) | Fair tapes almost surely have a stop after every offset, including the interleaved continuation-flag subsequences used by the binary sampler. The proof allows starting offsets chosen by earlier samples. |
| [TrialBounds.lean](ComplexityOfGenerators/Foundations/TrialBounds.lean), [TrialBoundExamples.lean](ComplexityOfGenerators/Proofs/TrialBoundExamples.lean) | Separate uniform polynomial seed and execution budgets; monotonicity of the execution allowance, exact full-seed witnesses, and preservation of Remark 1's emptiness test. A delayed empty generator now has a complete `PG` witness. |
| [EmptyTrialOverhead.lean](ComplexityOfGenerators/Proofs/EmptyTrialOverhead.lean) | A checked counterexample to the former equal-budget convention: one silent setup step followed by tape exhaustion is a genuine empty generator, but has no equal seed/transition bound at all. |
| [NonemptyTrialBounds.lean](ComplexityOfGenerators/Proofs/NonemptyTrialBounds.lean) | Nonempty slices have ordinary worst-case bounds on all finite tapes, including tapes longer than the seed budget. Collision slices satisfy this condition at every security parameter. |
| [BinaryCollisions.lean](ComplexityOfGenerators/Foundations/BinaryCollisions.lean) | A fixed two-bit encoding of the ternary collision alphabet, injectivity and exact decoding, malformed-input rejection, and nonempty binary collision slices of length `4 * (n + 1) + 2`. |
| [BinaryOutputDecoder.lean](ComplexityOfGenerators/Simulation/BinaryOutputDecoder.lean), [BinaryCollisionReduction.lean](ComplexityOfGenerators/Proofs/BinaryCollisionReduction.lean) | A concrete native streaming decoder with exact clock-by-clock correspondence, preserving the seed and runtime. Every full binary collision-generator trial yields a valid separated collision pair at the explicitly stated family index. |
| [ExecutionBounds.lean](ComplexityOfGenerators/Foundations/ExecutionBounds.lean) | Primitive-transition bounds on all read-only heads, work-head displacement, visited-cell count, output length, and consumed randomness. A random tape longer than the execution budget cannot be exhausted. The collision reduction uses this to prove correctness on every tape longer than the original generator's runtime. |
| [UnaryInput.lean](ComplexityOfGenerators/Simulation/UnaryInput.lean), [UnaryBlockLoader.lean](ComplexityOfGenerators/Simulation/UnaryBlockLoader.lean) | A concrete swap of unary ordinary input and the physical index tape, preserving every transition and outcome. The resulting loader prepares `4 * (n + 1) + 2` unary work-tape cells and rewinds in exactly `10 * n + 17` transitions. The complete generator simulation is implemented by the `VirtualIndex` modules below. |
| [PostTime.lean](ComplexityOfGenerators/Simulation/PostTime.lean) | Transfers Mathlib `StateTransition.EvalsToInTime` certificates for finite-control Post programs to native time bounds, with one native step per source step and the exact additional input-loading cost. It requires a time certificate for the source program; computability alone does not supply a polynomial bound. |
| [VirtualIndex.lean](ComplexityOfGenerators/Simulation/VirtualIndex.lean), [VirtualIndexTime.lean](ComplexityOfGenerators/Simulation/VirtualIndexTime.lean) | A concrete finite-control simulator with independently marked source work and unary-index heads. The scan, memory, fetch, return, work-step, and random-step proofs establish full outcome and output preservation on the same finite random tape. A `t`-step source execution uses at most `(t + 1) * (2 * t + 2 * indexLength + 8)` native simulation transitions. |
| [BlockMarker.lean](ComplexityOfGenerators/Simulation/BlockMarker.lean), [VirtualIndexBootstrap.lean](ComplexityOfGenerators/Simulation/VirtualIndexBootstrap.lean), [VirtualIndexPolynomial.lean](ComplexityOfGenerators/Simulation/VirtualIndexPolynomial.lean) | The full physical-index adapter starts on a blank work tape, expands `n` to `4 * (n + 1) + 2`, and hands the actual prepared tape to the simulator in `10 * n + 18` transitions. Mathlib polynomial arithmetic supplies a uniform polynomial bound for the complete machine, on every finite random tape. |
| [BinaryCollisionFinder.lean](ComplexityOfGenerators/Proofs/BinaryCollisionFinder.lean) | Constructs the native polynomial-time collision finder from a binary collision generator. Proves `h.CollisionResistant → h.binaryCollisionLanguage ∉ PG Bool` without an additional simulation hypothesis. |
| [PolynomialClockCorrectness.lean](ComplexityOfGenerators/Simulation/PolynomialClockCorrectness.lean), [BoundedNondeterministicRecognition.lean](ComplexityOfGenerators/Proofs/BoundedNondeterministicRecognition.lean) | A complete native polynomial clock: fixed-degree unary digit tracks, proved carry arithmetic, preservation of suspended source configurations, blank-tape loading and input-head restoration. Every choice tape halts within the proved polynomial, and accepted outputs are exactly those reached by the source deadline. This gives a native NP criterion from bounded accepting computations. |
| [GeneratorRecognizerCorrectness.lean](ComplexityOfGenerators/Simulation/GeneratorRecognizerCorrectness.lean), [PolynomialGenerationContainment.lean](ComplexityOfGenerators/Proofs/PolynomialGenerationContainment.lean) | Loads the exact virtual index `input.length`, restores the input head, simulates the generator and compares its output with the input using one finite-control Boolean. Proves `PG α ⊆ NP α` for every finite alphabet, including empty inputs, empty slices, and arbitrarily long choice tapes. No cryptographic assumption is used. |
| [CollisionVerification.lean](ComplexityOfGenerators/Proofs/CollisionVerification.lean) | An explicit Boolean collision-checking specification with proved correctness on every binary word. It checks the canonical pair encoding, preimage lengths and inequality, and the two native hash executions at their proved deadlines. |
| [TapeBankTime.lean](ComplexityOfGenerators/Simulation/TapeBankTime.lean) | Compiles a finite bank of work tapes into the retained native single-work-tape model. A bank execution of `t` instructions takes at most `1 + (t + 1) * (2 * t + 4)` native transitions, including initialization from a blank tape. The compiled transition table is deterministic in every state. |
| [CollisionParser.lean](ComplexityOfGenerators/Simulation/CollisionParser.lean), [CollisionHashPair.lean](ComplexityOfGenerators/Simulation/CollisionHashPair.lean) | A concrete seven-tape collision checker. Parsing, length/inequality validation, unary-index construction and input-head resets take at most `12 * (input.length + 1)` bank instructions. Both hash simulations, output resets and comparison take at most `12 * hash.time n + 5 * n + 10` more. Every malformed input rejects. |
| [PolynomialCollisionDecision.lean](ComplexityOfGenerators/Proofs/PolynomialCollisionDecision.lean) | Proves `HashFunction.binaryCollisionLanguage_mem_p` using the actual native compiled checker and a uniform polynomial bound. No extra closure, simulation, or cryptographic assumption is used. This completes Theorem 5.1 with the existing containment and collision-finder proofs. |
| [CryptographicReduction.lean](ComplexityOfGenerators/Proofs/CryptographicReduction.lean) | A finder correct on every full-budget seed succeeds with probability one and contradicts the exact collision-resistance assumption. The generic ternary reduction has an explicit simulation premise; `BinaryCollisionFinder` supplies the fully constructed binary attack. |

These modules are imported by `Foundations` and covered by the axiom audit.
The recursive-program compiler now proves native recognition on the original
word alphabet, and the local `RE` class agrees with Mathlib's recursively
enumerable word predicates. No polynomial bound is asserted for this composite
library compiler.

Theorem 3.1 is complete in both directions and its main declaration contains no
`sorry`. For `RE ⊆ GEN`, the construction samples a candidate code and a clock,
executes bounded recognition with a fixed language member as fallback, and emits
the result. Canonical binary sampling replaces the paper's choice of sampling
distribution; generability requires full support, not a particular distribution.
The fallback is fixed in the constructed program because the theorem asks for
existence of a generator; no uniform algorithm for choosing it is assumed.
The proof establishes this full support, probability-one acceptance, and halting
on **every** finite tape for the composed native transition table. The empty
language uses the separately proved tape-exhausting generator.

Theorem 5.1 is complete. The proof combines the native containment `pg_subset_np`,
the concrete collision decider `HashFunction.binaryCollisionLanguage_mem_p`, and
the constructed attack `HashFunction.binaryCollisionLanguage_not_mem_pg`.
Under the paper's collision-resistance assumption, the collision language lies
in `P` (and hence `NP`) but not in `PG`. All simulations start with blank native
work tapes and charge for initialization and head movement. The statement and
cryptographic assumptions are unchanged, and its transitive dependencies are
included in the axiom audit.

Complexitylib's multi-tape model, Mathlib's partial-recursive model and this
project's read-once-random-tape generator model have different representations.
Their polynomial-time and space classes are not yet proved equal. The `Standard` namespace names
the actual imported classes; the existing paper statements retain their local
definitions. `DecisionClassAgreement`, `SpaceGenerationBridge` and
`PolynomialGenerationBridge` are specifications for future simulation proofs,
with no assumed instance or unfinished proof filling their fields. Transport
results explicitly take these specifications as hypotheses.

The imported Savitch result proves polynomial-space class equality for
Complexitylib's machines. The native tape geometry and finite configuration
encoding are now verified, as is native `P ⊆ PSPACE` in
[NativeSpaceContainment.lean](ComplexityOfGenerators/Proofs/NativeSpaceContainment.lean).
[SpaceReachability.lean](ComplexityOfGenerators/Foundations/SpaceReachability.lean)
now proves exact correspondence between native acceptance and reachability in the
finite configuration graph. Every graph path is realized by a finite random tape;
[ExecutionPaths.lean](ComplexityOfGenerators/Foundations/ExecutionPaths.lean)
includes terminal successor configurations in the space accounting.
[SpaceCodeExecution.lean](ComplexityOfGenerators/Foundations/SpaceCodeExecution.lean)
provides effective transitions on finite codes, with proved encoding/decoding and
edge correspondence. No equality test on an infinite work tape is required.

[FiniteReachability.lean](ComplexityOfGenerators/Foundations/FiniteReachability.lean)
proves the vertex-count bound on path length and correctness of the Boolean
midpoint recursion. [SpaceSearch.lean](ComplexityOfGenerators/Foundations/SpaceSearch.lean)
applies this executable Lean search to the native configuration codes.
[OutputMatcherSpace.lean](ComplexityOfGenerators/Simulation/OutputMatcherSpace.lean)
proves that streaming output comparison preserves the exact work-space bound.
[PolynomialSpaceSearch.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceSearch.lean)
then gives a correct search for every polynomial-space generator's language,
with an explicit polynomial recursion-depth bound, including empty words and
empty slices.

[FixedWidthCodec.lean](ComplexityOfGenerators/Foundations/FixedWidthCodec.lean)
and [SpaceCodeBits.lean](ComplexityOfGenerators/Foundations/SpaceCodeBits.lean)
encode configuration fields individually in a bitstring of polynomial width.
Their base tests inspect only the endpoints and the two possible native
successors. [SavitchStack.lean](ComplexityOfGenerators/Foundations/SavitchStack.lean)
connects this graph to Complexitylib's verified Savitch stack interpreter,
reusing its midpoint counter, termination proof, and serialized-state bound.
Invalid encodings cannot introduce accepting paths. If configuration width is
at most recursion depth `d`, every serialized stack state has at most
`44 * (d + 1)^2` bits.
[PolynomialSpaceStack.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceStack.lean)
proves that this interpreter halts with the correct generator-membership answer
and has a uniform polynomial bound on its serialized states, even when source
branches loop. These results use the existing native generator assumptions.
The recursive finite-control program, input/root initializer, and complete
configuration-graph base program are implemented and connected to this
interpreter. The stack-to-native compiler converts their bounded traces into
actual visited-cell bounds, completing the machine-space containment.

The reusable space-preserving tape-bank compiler is now proved in
[TransducerBank/Space.lean](ComplexityOfGenerators/Simulation/TransducerBank/Space.lean).
A terminating finite tape-bank program whose reachable heads have radius `r`
compiles to the retained native machine using at most `2*r+1` visited work cells.
This bound covers initialization, scans, random reads, writes, and terminal
successors; it has no time-bound or random-tape-length premise.
[ExecutionRegions.lean](ComplexityOfGenerators/Foundations/ExecutionRegions.lean)
justifies bounding every execution prefix by its terminal visited set.
[NativeSpaceCompilation.lean](ComplexityOfGenerators/Proofs/NativeSpaceCompilation.lean)
packages actual deterministic bank programs with polynomial head bounds as
native `PSPACE` deciders.

[StackSpace/Native.lean](ComplexityOfGenerators/Simulation/StackSpace/Native.lean)
now provides an end-to-end, space-preserving compiler from Mathlib's finite
`TM2` programs with a common stack alphabet to the retained native model. The
compiler executes each
push, pop, peek, branch, local update and jump using an actual finite transition
table. Each stack is stored bottom-to-top; pops erase removed cells. The proof
covers input loading, acceptance and rejection, and every intermediate compiler
phase. If source stacks have length at most `s`, each source step stays within
tape-bank radius `s + C`, where `C` depends only on the fixed program text.
Arbitrarily many steps reuse that region. `StackSpace.mem_pspace` packages a
terminating source program with polynomially bounded stacks as a native
`PSPACE` decider. `StackSpace.mem_pspace_of_trace` permits the same conclusion
from compositional bounded execution traces.

[SavitchMachine/Counter.lean](ComplexityOfGenerators/Simulation/SavitchMachine/Counter.lean)
implements the midpoint increment and overflow flag as a finite Mathlib stack
program, proves exact agreement with Complexitylib's `bumpBits` and `bumpOver`,
and compiles its execution to the native single-work-tape machine with a fixed
region bound. This includes empty counters and overflow. These completed
compiler and counter results do not by themselves prove the forward inclusion.

[SavitchMachine/Program.lean](ComplexityOfGenerators/Simulation/SavitchMachine/Program.lean)
now supplies the finite recursive control table: child-frame construction,
both return branches, midpoint increments and overflow, frame popping, and
final halting. Its six frame columns and six scratch registers are manipulated
by checked cell-by-cell copy, transfer, comparison, and erasure loops.
[Execution.lean](ComplexityOfGenerators/Simulation/SavitchMachine/Execution.lean)
proves agreement with each active library step and every finite execution.
[WithInput.lean](ComplexityOfGenerators/Simulation/SavitchMachine/WithInput.lean)
extends this program with a persistent input stack, whose length is also
charged to the space bound. Recursive routines preserve it.

[PolynomialSpaceFrames.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceFrames.lean)
proves that the actual generator search satisfies the column bound and exact
midpoint-width invariant.
[PolynomialSpaceExecution.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceExecution.lean)
connects the recursive program to the correct generator-membership answer,
with an explicit obligation for the configuration-graph base-test subprogram.
The configuration-graph base subprogram remains to be implemented. It is not
hidden in a new assumption of Theorem 6.1. Input initialization and native
compilation are now supplied by the modules below.

The concrete constant-predicate base subprogram is proved correct and used in
[scripts/CheckSavitchMachine.lean](scripts/CheckSavitchMachine.lean) to execute
the complete recursive table. The checks cover both answers, zero-width
midpoints, overflow, nested recursion, scratch cleanup, and input preservation.
Run them with `lake env lean scripts/CheckSavitchMachine.lean`.

[SavitchMachine/Ruler.lean](ComplexityOfGenerators/Simulation/SavitchMachine/Ruler.lean)
implements polynomial ruler initialization as a finite program. It preserves
the input and constructs `c * (n + 1)^d` using unary counters, verified copying
loops and multiplication. Its bound includes the factor `n + 1`, which can
exceed a constant polynomial. The same script checks empty inputs, constant
bounds and repeated multiplication.

[Initialize.lean](ComplexityOfGenerators/Simulation/SavitchMachine/Initialize.lean)
now composes the input loader, polynomial rulers, native initial-configuration
encoder and root-frame assembler into one finite program, with a proved
polynomial bound. It supports arbitrary input letters using a disjoint work
alphabet. [PolynomialSpaceInitialization.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceInitialization.lean)
proves that its endpoint is exactly `generatorStackRun … 0`.
[PolynomialSpaceDecision.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceDecision.lean)
then joins initialization to recursive search and compiles the entire program
into the retained single-work-tape model. Its theorem
`generator_language_mem_pspace_of_base` has one explicit implementation premise:
a finite configuration-graph base program with the specified correctness and
space bound. That program has not yet been constructed.

[CoordinateDecode.lean](ComplexityOfGenerators/Simulation/SavitchMachine/CoordinateDecode.lean)
implements the existing fixed-width coordinate codec, including wrong-length
and out-of-range rejection. It clamps after each binary digit so malformed
midpoints cannot allocate exponential unary storage. The unary-to-binary
encoder reuses Complexitylib's verified counter. The general stack routine
embedding and alphabet transport preserve space bounds, and the native input
adapter preserves the exact visited-cell set, including terminal successors.

The native configuration-test components now include sequential field reading,
affine header lookup, input and unary-index observations, work-head and tape
validation, clamped read-only head movement, strict work-head movement, and
single-cell tape-update comparison. In particular,
[ConfigurationHeader.lean](ComplexityOfGenerators/Simulation/SavitchMachine/ConfigurationHeader.lean)
connects the composed header reader and head comparison to the existing typed
configuration codec. [WorkObservation.lean](ComplexityOfGenerators/Simulation/SavitchMachine/WorkObservation.lean)
composes head decoding, window location and cell validation, preserving the
original input even on rejection.
[SpaceCodeLocal.lean](ComplexityOfGenerators/Foundations/SpaceCodeLocal.lean)
proves that native graph edges are exactly the corresponding local state,
head and work-array comparisons.
[PolynomialSpaceBaseBounds.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceBaseBounds.lean)
shows that their coordinate counters, header offsets and window storage fit
the already chosen polynomial stack bound. All these are completed proofs,
with no additional axioms or unfinished sublemmas.

Endpoint loading and cache cleanup preserve suspended parent frames and the
persistent input. [BooleanTest.lean](ComplexityOfGenerators/Simulation/SavitchMachine/BooleanTest.lean)
composes these restorative tests without additional registers.
[ObservationQueries.lean](ComplexityOfGenerators/Simulation/SavitchMachine/ObservationQueries.lean)
implements acceptance leaves, and [EdgeQueries.lean](ComplexityOfGenerators/Simulation/SavitchMachine/EdgeQueries.lean)
implements equality or one native transition, including malformed-code rejection.
[GraphBase.lean](ComplexityOfGenerators/Simulation/SavitchMachine/GraphBase.lean)
selects the appropriate test and removes the completed frame.
[PolynomialSpaceBase.lean](ComplexityOfGenerators/Proofs/PolynomialSpaceBase.lean)
discharges `generator_language_mem_pspace_of_base` and proves `pspaceg_subset_pspace`.

Acceptance leaves test their current configuration; reachability leaves allow
zero or one edge. The verified acceptance recursion therefore covers paths of
length at most `2^depth - 1`. The sharpened finite-graph bound proves that every
reachable vertex has a path shorter than the vertex count, so the existing
polynomial recursion depth suffices. This is an implementation choice within
Savitch's argument, with no change to Theorem 6.1 or the native complexity classes.
[scripts/CheckConfigurationTests.lean](scripts/CheckConfigurationTests.lean)
executes the actual component tables on valid and malformed headers and windows,
input and work-head boundaries, distinct original input letters, and permitted
or forbidden writes. Run it with `lake env lean scripts/CheckConfigurationTests.lean`.

[scripts/CheckSpaceInitialization.lean](scripts/CheckSpaceInitialization.lean)
executes the composed initializer and decoder on empty inputs, distinct input
and interpreter alphabets, constant and nonconstant bounds, malformed fields,
and coordinate overflow. Run it with
`lake env lean scripts/CheckSpaceInitialization.lean`.

The reverse direction is now completely proved in
[SpaceGeneration.lean](ComplexityOfGenerators/Proofs/SpaceGeneration.lean):
`pspace_subset_pspaceg : PSPACE α ⊆ PSPACEG α`. The finite program and its proofs
are in [CyclicGenerator](ComplexityOfGenerators/Simulation/CyclicGenerator).
It follows Appendix A.17: a word counter enumerates candidates, the source
decider tests each candidate, a fair coin offers each accepted word, and
nonempty passes restart. Empty passes drain the random tape. Two virtual tapes
hold only the current word and the decider's work; touched-cell markers allow
work memory to be erased and reused between tests.

The proof checks initialization, the four-instruction simulation of each source
step, erasure and rewinding, counter coverage and overflow, selection, and output.
For source space `s(n)`, the native machine visits at most
`10 * (n + s(n) + 1) + 1` cells, independently of runtime and seed length.
It terminates on every finite seed without explicit rejection, has exactly the
requested language slice as support, and accepts almost every fair stream when
that slice is nonempty. The empty word is handled directly; over an empty
alphabet the existing empty-language and empty-word generators use one cell.
[RegionSteps.lean](ComplexityOfGenerators/Simulation/TransducerBank/RegionSteps.lean)
provides the composable fixed-region paths and complete executions used to
compile this construction into native visited-cell bounds.

Together, `pspaceg_subset_pspace` and `pspace_subset_pspaceg` prove Theorem 6.1.
The result is the paper's unrelativised equality of polynomial-space language
classes. The proof does not assert Proposition 6.5's oracle-relativised equality
or a separate sharp `s²` native bound.

For Theorem 7.1,
[CertificateVerifier.lean](ComplexityOfGenerators/Simulation/CertificateVerifier.lean)
compiles native choice-tape machines into deterministic certificate readers,
with an exact one-step-per-step simulation and exhaustion changed to rejection.
[PolynomialVerifiers.lean](ComplexityOfGenerators/Proofs/PolynomialVerifiers.lean)
proves `np_has_polynomialVerifier` and `pg_has_polynomialVerifier`, with positive
certificates of polynomial length.

[TranscriptSampling.lean](ComplexityOfGenerators/Proofs/TranscriptSampling.lean)
and [TranscriptRecovery.lean](ComplexityOfGenerators/Proofs/TranscriptRecovery.lean)
now construct the native forward sampler and recoverer. Certificates have one
padding bit followed by one bit per source step. The sampler takes at most
`2t+1` steps for a `t`-step source run and preserves acceptance on the same
random tape, hence almost-sure productivity. Replay consumes certificate fuel
on every step, so it terminates even on malformed certificates. The recoverer
turns replay rejection into random-tape exhaustion and has seed bound one and
time bound `n+|c|+1`. All sampled certificates recover an instance of length `n`,
and their recovered languages together equal the source slice, including at
`n=0`. Every source word also has a polynomial-length recovery certificate.

[PolynomialCertificateSchemes.lean](ComplexityOfGenerators/Proofs/PolynomialCertificateSchemes.lean)
constructs the required deterministic polynomial verifier: it counts the input,
replays the certificate with the virtual unary index, and compares the full output.
It assembles the transcript machines into a certificate scheme.

[CertificateSchemeGeneration.lean](ComplexityOfGenerators/Proofs/CertificateSchemeGeneration.lean)
proves the reverse implication. It clocks the sampler and composes it with the
recoverer using a verified four-tape bank, compiled to the retained one-work-tape
machine. The proof accounts for certificate storage, rewinding, shared random-tape
consumption, empty slices, and polynomial seed and execution bounds. Every sampled
certificate certifies an instance, so every actual recovery call has the required
polynomial bound. Neither direction assumes a simulation compiler as an axiom.

The composition and fallback proofs share the criteria in
[GeneratorCriteria.lean](ComplexityOfGenerators/Proofs/GeneratorCriteria.lean):
`Machine.isGenerator_of_full_trials` handles the probability argument, and
`mem_pg_of_lengthSlices` packages the native machine as a polynomial generator.
The clocked sampler's support equality is exposed by `familyClock_generatedLanguage`.
The fallback instruction and native-time polynomials have separate names so their
cost estimates can be read without repeating the full expressions. These helpers
preserve the original machine constructions and exact resource bounds.

For Theorem 7.2,
[FallbackGeneration.lean](ComplexityOfGenerators/Proofs/FallbackGeneration.lean)
proves that every native NP language `L` has polynomial generators for both
`L ∪ 0⁺` and `L ∪ 1⁺`. The finite program samples a word, runs a nondeterministic
decision branch, and emits either the accepted word or the constant fallback.
It handles the empty word separately, has no explicit rejection, and satisfies
the separate polynomial seed and execution bounds.

[NondeterministicUnion.lean](ComplexityOfGenerators/Proofs/NondeterministicUnion.lean)
proves native NP union closure using a verified one-bit branch choice.
[GeneratorNonclosure.lean](ComplexityOfGenerators/Proofs/GeneratorNonclosure.lean)
then proves both contradictions. Complement closure of PG would put the union
of the two fallback-language complements in NP; that union is `Lᶜ`, so
`NP = coNP`. Intersection closure would put the secure collision language in PG,
because `(L ∪ 0⁺) ∩ (L ∪ 1⁺) = L`, contradicting Theorem 5.1's collision-finder
reduction. The two conclusions retain their independent original assumptions.

## Theorem correspondence

The printed page numbers below are the paper's `0:…` numbers, not PDF array indices.
Every declaration includes the paper's statement and number in its docstring.

| Paper | Lean declaration in [MainTheorems.lean](ComplexityOfGenerators/MainTheorems.lean) | Statement and assumptions |
| --- | --- | --- |
| Theorem 3.1, 0:10 | `theorem_3_1_generability_is_recursive_enumerability` | `RE α = GEN α`, for a finite alphabet. |
| Theorem 5.1, 0:15 | `theorem_5_1_cryptographic_separation` | Collision-resistant hashes imply `PG Bool ⊂ NP Bool` **and** `¬ P Bool ⊆ PG Bool`. |
| Theorem 6.1, 0:22 | `theorem_6_1_polynomial_space_generation` | `PSPACEG α = PSPACE α`, without an oracle or additional assumption. |
| Theorem 7.1, 0:24 | `theorem_7_1_generators_are_certificate_schemes` | `L ∈ PG α ↔ ∃ V : PolynomialVerifier L, HasCertificateScheme V`. The verifier is existential, and `L ∈ NP` is not an extra hypothesis. |
| Theorem 7.2, 0:25 | `theorem_7_2_efficient_generators_are_not_composable` | `NP Bool ≠ coNP Bool` implies failure of complement closure; independently, collision-resistant hashes imply failure of intersection closure. |

Lemmas, propositions, corollaries, examples, remarks, and references to other
authors' theorems are outside the requested main-theorem inventory.

## Definitions and modelling choices

- [Machine.lean](ComplexityOfGenerators/Machine.lean) gives an operational machine
  with finite control and finite alphabets. It has one work tape, read-only inputs,
  a read-once random tape, and an append-only output tape. A transition cannot
  invoke an arbitrary computation. Ordinary unary input uses `List Unit`, and
  the dedicated index exposes `Option Unit`: `some ()` is a mark and `none` is
  blank. These remain separate tapes with independent heads; `InputData.index`
  stores the index length as a natural number. The unary adapter swaps symbols
  directly. Simulators may store marks as Boolean occupancy flags or binary
  cells, which they explicitly decode at the native machine boundary. Random
  bits, certificates, and ordinary binary inputs retain their Boolean alphabets.
  Unused inputs are empty. Halting observations
  take no extra transition; work-tape space includes cells visited immediately
  before halting. Equivalence with the paper's tape conventions remains a future
  proof obligation.
- [Generators.lean](ComplexityOfGenerators/Generators.lean) uses the actual
  infinite product of uniform Boolean probability measures. A generator must
  halt on every finite tape, reject only by exhaustion, and have acceptance
  probability **one or zero**. Language membership means support, with no
  uniformity or lower bound on individual output probabilities. Accepted streams
  use all accepted prefixes; for read-once machines this is the same union of
  cylinders as the paper's minimal-prefix construction. This equality is now
  proved in `Proofs.GeneratorSupport`.
- A uniform family is **one** machine reading the unary index, not an arbitrary
  map from indices to unrelated machines. `GeneratorFamily` enforces exact output
  length. `UniformGenerators` also supports certificate samplers whose output
  length need not equal their index. Length-zero slices are included.
- [ComplexityClasses.lean](ComplexityOfGenerators/ComplexityClasses.lean) defines
  recognisers and deterministic/nondeterministic decision classes independently
  of generation classes. Polynomial bounds take the cofinal form
  `c * (n + 1)^k`, with positive `c`; bivariate bounds use
  `c * (n + m + 1)^k`. This absorbs constants and handles size zero. Establishing
  equivalence with the paper's full asymptotic conventions is future work;
  domination of natural-coefficient polynomials is now proved in
  `Foundations.ResourceBounds`.
- Time-bounded generation follows **Remark 1**, with the user's approved
  separation of seed and execution budgets. One polynomial `r(n)` bounds random
  tape length; another polynomial `t(n)` bounds primitive transitions. Every
  trial on at most `r(n)` bits halts within `t(n)` steps. Every full trial of
  exactly `r(n)` bits accepts iff the slice is nonempty; otherwise it rejects
  by exhaustion. This is explicit in `Machine.GeneratorTimeBound`. The proof
  `bounded_trial_exhausted_iff_empty` preserves the Remark 1 emptiness test.
  Neither bound permits an arbitrary computation inside a machine transition.
  Certificate recovery uses separate polynomial budgets in both input lengths too.
- [Cryptography.lean](ComplexityOfGenerators/Cryptography.lean) retains unkeyed
  hashes, a single uniform polynomial implementation, uniform randomised attacks,
  inverse-polynomial success, the strict probability inequality, and **infinitely
  many** security parameters. Hash domains and codomains are typed as `n+1` and `n`
  bits. Collision attacks output a pair separated by a reserved symbol. Their
  outputs are not required to be correct, or productive, as generators are.
- [Certificates.lean](ComplexityOfGenerators/Certificates.lean) records verifier
  completeness with a polynomial certificate bound, soundness for every positive
  certificate, certificate-sampler coverage at the requested instance length,
  a certified instance for every sampled certificate, rejection on empty slices,
  and uniform recovery for every positive certificate
  with a time bound polynomial in both size and certificate length.
- Certificates are bitstrings, and verifier word/certificate inputs occupy
  separate read-only tapes. This is an explicit encoding of `w#c`. The usual
  constant-factor equivalence of certificate alphabets presumes an alphabet with
  at least two symbols; it is not a proved encoding theorem in this development.
  The cryptographic and nonclosure theorems use binary word languages; the other
  statements are parameterised by a finite output alphabet.
- Complementation is relative to all finite words, including malformed encodings.
  Theorem 7.2 states language closure; it does not assert a uniform compiler for
  predicate syntax or add an NP-completeness assumption to its statement.

## Source issues retained or made explicit

1. **Empty slices and time.** A literal runtime bound independent of arbitrary
   finite random-tape length would exclude empty generators, which must consume
   the tape before rejecting. Bounded trials implement Remark 1 instead. The
   initial implementation used the same value for seed length and primitive
   runtime; the checked `delayedEmptyGenerator_not_generatorTimeBound` shows that
   even one setup step then destroys every such bound. At the user's direction,
   the definition now uses separate uniform polynomial seed and execution
   budgets. This permits simulation overhead while preserving exhaustion and
   the full-trial emptiness test. It is a documented interpretation, not a proof
   that the paper's literal equal-budget wording is equivalent.
2. **Hash indexing.** Definition 5.3 types `h_n` on `n+1`-bit inputs, while
   Definition 5.5 uses `h_|x|(x)`. That application is ill-typed. `IsCollision`
   follows Definition 5.3: a collision of `h_n` has two `n+1`-bit preimages. No
   auxiliary collision-language lemma is assumed to prove Theorem 5.1.
3. **Theorem 7.1 and the empty word.** Definition 7.3 says `w ∈ α⁺`, not `α*`.
   That original restriction prevents certificate coverage for a language
   containing the empty word. `empty_word_language_in_pg` supplies the actual
   uniform native generator for `{ε}`, with both polynomial budgets constant
   one, for every finite alphabet (including an empty alphabet).
   `literal_certificate_coverage_characterization_false` checks the resulting
   counterexample. At the user's direction, `certifiedInputs` now allows empty
   instance words. `LiteralCertificateCoverage` retains the old restriction
   solely to document the counterexample.
4. **Certificate composition.** Definition 7.4 does not require *every* sampled
   certificate to certify a length-`n` instance. Definition 7.5 permits an empty
   recovery fibre. Appendix A.20's direct composition argument therefore needs
   a correction: a sampled certificate with an empty fibre can cause recovery
   to exhaust its input. At the user's direction, the new
   `CertificateGenerator.certifiesInstance` field requires every sampled
   certificate to certify a length-`n` instance. Checked consequences include
   positivity of sampled certificates, nonempty recovery languages, and
   acceptance of every full-budget recovery trial. Arbitrary certificates may
   still have empty recovery languages, as in Definition 7.5.
