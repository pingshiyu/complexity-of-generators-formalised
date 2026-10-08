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

Theorems 6.1, 7.1 and 7.2 remain unfinished and contain `sorry`. All supporting
lemmas have complete proofs; no custom axioms are introduced. A successful build
does not establish these three remaining results.

**Theorem 7.1 uses two user-approved corrections to the certificate definitions:**
certified instances may be empty words, and every sampled certificate must
certify an instance of the requested length. Certificates remain positive strings.
[EmptyWordGeneration.lean](ComplexityOfGenerators/Proofs/EmptyWordGeneration.lean)
proves why the original coverage condition needs correction: `{ε} ∈ PG`, but
`LiteralCertificateCoverage` cannot cover its size-zero slice. The counterexample
concerns that historical condition, not the corrected `HasCertificateScheme`.
The `sorry` in Theorem 7.1 is not used by any supporting proof.

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

Import `ComplexityOfGenerators` to obtain the entire development. The compiler
will report three expected `declaration uses 'sorry'` warnings. Upstream VCVio
also emits deprecation warnings. The first build compiles the imported
Complexitylib and VCVio modules that are not covered by Mathlib's cache.

The root Lake post-update hook applies a small, verbatim upstream proof
compatibility backport to Complexitylib. It changes four cast proofs and no
statements or definitions; see [patches/README.md](patches/README.md). Lake's
warning that Complexitylib has local changes refers to this recorded backport.

Import `ComplexityOfGenerators.Foundations` to use the supporting development
without importing the unfinished main theorems. The audit traverses the axiom
dependencies of every declaration in those local modules, including the imported
proofs they use, and explicitly checks the completed main Theorems 3.1 and 5.1.
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

### Completed proof components and remaining obligations

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
The space-preserving simulations needed to apply Savitch to Theorem 6.1 remain
unfinished. No quantitative `s²` bound for the local machine, or
oracle-relativised result, is claimed. Polynomial-space generator constructions
and the certificate sampler/recoverer constructions remain unfinished. The source
issues and approved definition corrections are recorded below.

For Theorem 7.1,
[CertificateVerifier.lean](ComplexityOfGenerators/Simulation/CertificateVerifier.lean)
compiles native choice-tape machines into deterministic certificate readers,
with an exact one-step-per-step simulation and exhaustion changed to rejection.
[PolynomialVerifiers.lean](ComplexityOfGenerators/Proofs/PolynomialVerifiers.lean)
proves `np_has_polynomialVerifier` and `pg_has_polynomialVerifier`, with positive
certificates of polynomial length. The corrected sampler/recoverer definitions
also yield the exact union of recovered languages and a uniform polynomial time
bound on all sampled recovery calls. These results do not yet construct the
native composed generator or the forward sampler and recoverer. Theorem 7.2's
closure constructions also remain unfinished.

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
  invoke an arbitrary computation. Unused inputs are empty. Halting observations
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
