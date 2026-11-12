# Current paper definitions and Lean implementations

This guide follows the current PLDI27 source, as examined on 12 November 2026.
The bundled PDF is an older manuscript. See [result status](CURRENT_PAPER_STATUS.md)
for theorem coverage; the existence of a definition does not mean all results
about it have been formalised.

| Paper object | Lean implementation | Convention or limitation |
| --- | --- | --- |
| Finite words / languages | `Word α`, `Language α`, `LanguageClass α` in [Machine](ComplexityOfGenerators/Machine.lean) | Lists and sets of lists; the empty word and empty finite alphabet are included |
| Bitstring transducer | `Machine`, `Instruction`, `Configuration` | Finite transition table; one two-way work tape; ordinary, auxiliary and unary-index read-only tapes; read-once random tape and append-only output |
| Time / work space | `Machine.run`, `Machine.TimeBound`, `Machine.SpaceBound` | Primitive transitions; terminal observation costs no additional transition; all visited work cells count, including the initial cell |
| Halting transducer | `Machine.HaltingTransducer` in [Generators](ComplexityOfGenerators/Generators.lean) | All finite seeds halt; explicit rejection is forbidden; missing random bits cause exhaustion |
| Fair streams and cylinders | `fairCoinMeasure`, `cylinder` | Uniform independent Boolean product measure; cylinder measurability and mass proved |
| Generator | `Machine.IsGenerator` | Halting transducer with accepted-stream measure zero or one; zero represents empty support |
| Generated language | `Machine.generatedLanguage` | Nonempty finite seed witnesses; seed-extension proves that outputs witnessed by the empty seed are included as well |
| Infinite-stream output/runtime | [StreamSemantics](ComplexityOfGenerators/Foundations/StreamSemantics.lean) | Length is zero when no output is produced; runtime is infinite on divergence; both measurable and derived from the native evaluator |
| Uniform family | `UniformGenerators` | One native machine for every unary index |
| Exact family | `GeneratorFamily` | Every supported output at index `n` has length `n` |
| Accepting-time bound | `Machine.AcceptingTimeBound`, `UniformGenerators.AcceptingPolynomialTime` in [ResourceGeneration](ComplexityOfGenerators/Proofs/ResourceGeneration.lean) | Only accepting runs are bounded; no bound on draining arbitrarily long seeds of an empty member |
| Historical finite-trial budget | `Machine.GeneratorTimeBound`, `UniformGenerators.PolynomialTime` | Separate seed/execution budgets; full-budget acceptance iff nonempty support. [AcceptingTimeGeneration](ComplexityOfGenerators/Proofs/AcceptingTimeGeneration.lean) proves agreement with the current convention for PG |
| `GTIME` / `GSPACE` | [ComplexityClasses](ComplexityOfGenerators/ComplexityClasses.lean) | Unary-index native resource classes; GTIME bounds accepting runs only. The separate explicit multitape classes below carry the general resource results |
| General multitape resources | [MultitapeModel](ComplexityOfGenerators/MultitapeModel.lean), [MultitapeComplexityClasses](ComplexityOfGenerators/MultitapeComplexityClasses.lean), [MultitapeConstructibility](ComplexityOfGenerators/MultitapeConstructibility.lean) | Actual finite work-tape bank, stored finite input/work/output/control alphabets, unit-cost bank instructions, eventual multiplicative resource bounds. Charged time/space constructors, binary index simulation and configuration clocks prove the complete general TIME/SPACE containments and up-to equalities |
| Up-to family | `upToSlice`, `UpToGeneratorFamily`, `PGUpTo`, `PSPACEGUpTo` in [UpToGeneration](ComplexityOfGenerators/Proofs/UpToGeneration.lean) | Exact cumulative support; complete polynomial-time and polynomial-space equalities; general resource equalities hold in the explicit multitape classes |
| `RE`, `P`, `NP`, `coNP`, `PSPACE`, `PG` | [ComplexityClasses](ComplexityOfGenerators/ComplexityClasses.lean) | Native finite-control classes; not assumed equal to imported Complexitylib classes. Native RE agreement with Mathlib recursively enumerable predicates is proved |
| Expected polynomial-time exact generation | `EPG`, `UniformGenerators.ExpectedPolynomialTime` in [ExpectedGenerators](ComplexityOfGenerators/ExpectedGenerators.lean) | Expected runtime bounded on nonempty members, plus one polynomially short accepting path for every supported word; exact lengths; finite languages allowed |
| Nonempty indices `I_G` | `UniformGenerators.activeIndices` | `{n \| (G.layer n).Nonempty}` |
| Raw expected-length/expected-time generation | `ExpectedLengthExpectedPolynomialTime`, `ExpectedLength`, `RawExpectedPolynomialTime` | Infinite language and active-index set; mean/runtime constraints only at active indices; no fast-path restriction |
| ELEPG | `ELEPG`, `GlobalWordPolynomialTime` | Raw moment conditions, infinitely many active indices, and for every generated word a polynomial-in-word-length fast accepting run at some index. `bounded_paths` derives a polynomial index bound by unary-index locality |
| Historical layer-fast variant | `LayerFastELEPG`, `PolynomialIndexCoverage` | Stronger family requirements retained under a distinct name: fast runs for every word in every layer plus polynomial producing-index coverage |
| Collision resistance | [Cryptography](ComplexityOfGenerators/Cryptography.lean) and [foundations](ComplexityOfGenerators/Foundations/Cryptography.lean) | Uniform unkeyed hash family; native polynomial attackers; verified agreement with the corresponding VCVio security quantifiers |
| Collision language | `HashFunction.binaryCollisionLanguage` | Fixed injective two-bit-block encoding of bits/separator. Parameter `n` gives encoded length `4*(n+1)+2`, rather than the paper's ternary length `2*n+3` |
| Polynomial certificate schemes | [Certificates](ComplexityOfGenerators/Certificates.lean) | Native verifier/sampler/recoverer. Historical positive binary certificates remain; paper now permits empty certificates and uses its own alphabet. An explicit convention-equivalence bridge is still needed |
| Self reduction / exact recursion | [SelfReducibility](ComplexityOfGenerators/SelfReducibility.lean) | Concrete native computational hypotheses. Inverse labels are still accepted at all lengths; the proof enumerates a logarithmic range. Restriction to the paper's explicit bounded-label interface remains an API alignment obligation |
| SAT construction | [SAT](ComplexityOfGenerators/Examples/SAT.lean), [inversion](ComplexityOfGenerators/Examples/SATInversion.lean) | Concrete padded syntax, substitution, certificates, inverse choices and fibre laws; native polynomial self-reduction, full-support base/inverse machines, `PaddedCNF.exactlyRecursivelyGenerable`, and `PaddedCNF.language_mem_pg` checked. On malformed words, Lean retains the parsed header rank, while the paper assigns rank/width zero; valid encodings and the self-reduction laws agree |
| HAMPATH construction | [HAMPATH](ComplexityOfGenerators/Examples/HAMPATH.lean), [paths](ComplexityOfGenerators/Examples/HAMPATHPaths.lean), [inversion](ComplexityOfGenerators/Examples/HAMPATHInversion.lean), [native machines](ComplexityOfGenerators/Examples/HAMPATHNative.lean) | Concrete matrix codec, order-preserving vertex insertion/deletion, path laws, ranks and inverse fibres; native polynomial self-reduction, full-support base/inverse machines, `HAMPATH.exactlyRecursivelyGenerable`, and `HAMPATH.language_mem_pg` checked |

## Scope of model comparisons

The native model uses unary family indices and clamped read-only input heads.
The paper's current closure proof uses unary indices and a moving controller
for unbounded expected-time calls. Existing verified stack/tape-bank compilers
have quadratic overhead in the source execution length. Polynomial worst-case
bounds survive this overhead. The checked EPG and historical layer-fast union, concatenation and star
constructions normalise each source to independent bounded phases and use
geometric retry second moments. They are not the current ELEPG closure proofs.
For current ELEPG, direct original-source sampling preserves first moments;
the moving packet simulator and outer controller have checked native finite
executions, full support, halting and expected-cost bounds. `ELEPGBinary` and
`ELEPGStar` package all three current closure theorems. No source variance
hypothesis is added.
General TIME and SPACE containments and both converse up-to constructions are
checked in the explicit finite multitape model. The clock and index operations
are actual finite transition routines, and their time/space costs are charged.

The unused `ModelBridge` specifications were removed. Their fields were future
construction goals, including an assumed SAT generator; they were never proofs
of those goals. Complete native theorems instead use the actual translators and
programs identified in their proof modules.

## Theorem entry points

`MainTheorems.lean` collects the current PLDI27 results, resource
specialisations and concrete SAT/HAMPATH constructions. `HistoricalTheorems.lean`
retains older theorem names and numbering, including certificate-scheme
equivalence under the positive binary certificate convention. The root package
imports both; importing `MainTheorems` alone supplies the current API.
