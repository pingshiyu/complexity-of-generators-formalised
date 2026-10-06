# Complexity of generators, formalised

Lean 4 formalisation of *Complexity Theory of Randomised Testing*,
using the supplied [paper](complexity-of-generators-formalisation.pdf).

**Status:** all five results labelled “Theorem” have declarations, with concrete
definitions of their terms. Their proofs are intentionally unfinished (`sorry`),
as requested for the statement pass. The supporting development now imports
proved complexity results from Complexitylib and cryptographic security machinery
from VCVio. All new supporting lemmas have complete proofs. A successful build
does not establish the five main theorems. No custom axioms are introduced.

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
will report five expected `declaration uses 'sorry'` warnings. Upstream VCVio
also emits deprecation warnings. The first build compiles the imported
Complexitylib and VCVio modules that are not covered by Mathlib's cache.

The root Lake post-update hook applies a small, verbatim upstream proof
compatibility backport to Complexitylib. It changes four cast proofs and no
statements or definitions; see [patches/README.md](patches/README.md). Lake's
warning that Complexitylib has local changes refers to this recorded backport.

Import `ComplexityOfGenerators.Foundations` to use the supporting development
without importing the unfinished main theorems. The audit traverses the axiom
dependencies of every declaration in those local modules, including the imported
proofs they use. It rejects `sorryAx`, custom axioms and unchecked evaluation
axioms; only `propext`, `Classical.choice` and `Quot.sound` are allowed.

## Supporting machinery

| File | Definitions and proved results | Use in the paper |
| --- | --- | --- |
| [Classical.lean](ComplexityOfGenerators/Foundations/Classical.lean) | Direct aliases of Complexitylib's `P`, `NP`, `coNP`, `PSPACE`, `NPSPACE`, `L`, `NL`, time/space classes, `FP`, Karp reductions and completeness. | Classical complexity terminology throughout. |
| [BasicTheorems.lean](ComplexityOfGenerators/Foundations/BasicTheorems.lean) | Imported proofs of `P ⊆ NP`, `P ⊆ PSPACE`, complement closure of `P`, time-to-space containment, `NL ⊆ P`, Cook–Levin, UNSAT coNP-completeness, `UNSAT ∈ NP ↔ NP = coNP`, and `PSPACE = NPSPACE`. | Theorems 5.1, 6.1 and 7.2. |
| [Computability.lean](ComplexityOfGenerators/Foundations/Computability.lean) | Mathlib encodings, partial-recursive enumerability, computable predicates and many-one reductions; imported proofs of Post's theorem and the halting problem. Mathlib's polynomial-time TM interface is exposed too. | Computability foundations for Theorem 3.1. |
| [ResourceBounds.lean](ComplexityOfGenerators/Foundations/ResourceBounds.lean) | Positive polynomial bounds, conversion to Mathlib polynomials, domination of every natural-coefficient polynomial, and bounds for addition, multiplication and composition. | Resource accounting for verifiers, samplers, recovery and reductions. |
| [Cryptography.lean](ComplexityOfGenerators/Foundations/Cryptography.lean) | Collision language, pigeonhole collision existence at every parameter, nonempty slices, injective pair codec, and a proved equivalence of the paper's assumption with VCVio's `SecurityGame.secureAgainst` and `negligible`. | Collision-resistance assumptions in Theorems 5.1 and 7.2. |
| [Probability.lean](ComplexityOfGenerators/Foundations/Probability.lean) | Fair-coin probability measure, cylinder mass `2⁻ᵏ`, and measurability of acceptance and collision-success events. | The probability semantics of generators and attackers. |
| [ModelBridge.lean](ComplexityOfGenerators/Foundations/ModelBridge.lean) | Explicit comparison interfaces and proved conditional transport of Savitch and the complement-nonclosure argument. | Records which generator-specific simulations remain to be constructed. |

The VCVio equivalence preserves unkeyed hashing and uniform polynomial-time
attackers, and proves both directions of the exact eventual/infinite-size
quantifiers. It does not add keyed hashing, nonuniform circuits or a new security
assumption. VCVio's imported game-reduction and polynomial-loss lemmas are then
available for subsequent cryptographic reductions.

### Remaining construction obligations

Complexitylib's multi-tape model, Mathlib's partial-recursive model and this
project's read-once-random-tape generator model have different representations.
Their decision classes are not yet proved equal. The `Standard` namespace names
the actual imported classes; the existing paper statements retain their local
definitions. `DecisionClassAgreement`, `SpaceGenerationBridge` and
`PolynomialGenerationBridge` are specifications for future simulation proofs,
with no assumed instance or unfinished proof filling their fields. Transport
results explicitly take these specifications as hypotheses.

The imported Savitch result proves the polynomial-space class equality required
by unrelativised Theorem 6.1. No quantitative `s²` bound for the local machine, or
oracle-relativised result, is claimed. Generator-specific constructions, the
collision-language complexity bounds and security reductions, and the
certificate constructions remain for the main-proof stage. The source issues
below also remain unresolved.

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
  cylinders as the paper's minimal-prefix construction. That equivalence has not
  yet been proved here.
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
- Time-bounded generation follows **Remark 1**, as clarified in this session.
  Every trial on a tape of at most `p(n)` bits halts within `p(n)` transitions.
  Every trial on exactly `p(n)` bits accepts iff the length slice is nonempty.
  Otherwise it rejects by exhaustion. This is explicit in
  `Machine.GeneratorTimeBound`; no bound independent of random-tape length is
  imposed on consuming arbitrarily long tapes of an empty generator. Decision
  algorithms use ordinary worst-case time bounds on all finite choice tapes.
  The proved lemma `bounded_trial_exhausted_iff_empty` verifies that a full-budget
  trial exhausts its tape exactly when the generated slice is empty.
- [Cryptography.lean](ComplexityOfGenerators/Cryptography.lean) retains unkeyed
  hashes, a single uniform polynomial implementation, uniform randomised attacks,
  inverse-polynomial success, the strict probability inequality, and **infinitely
  many** security parameters. Hash domains and codomains are typed as `n+1` and `n`
  bits. Collision attacks output a pair separated by a reserved symbol. Their
  outputs are not required to be correct, or productive, as generators are.
- [Certificates.lean](ComplexityOfGenerators/Certificates.lean) records verifier
  completeness with a polynomial certificate bound, soundness for every positive
  certificate, certificate-sampler coverage at the requested instance length,
  rejection on empty slices, and uniform recovery for every positive certificate
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

1. **Empty slices and time.** Taken literally on arbitrarily long finite random
   tapes, Definitions 2.3 and 4.3 would exclude empty generators from every bounded
   time class: they must consume the tape before rejecting. The bounded-tape trial
   interpretation above follows Remark 1 and the user's clarification. It is a
   documented interpretation, not a claim that the literal universal bound is
   equivalent for empty slices.
2. **Hash indexing.** Definition 5.3 types `h_n` on `n+1`-bit inputs, while
   Definition 5.5 uses `h_|x|(x)`. That application is ill-typed. `IsCollision`
   follows Definition 5.3: a collision of `h_n` has two `n+1`-bit preimages. No
   auxiliary collision-language lemma is assumed to prove Theorem 5.1.
3. **Theorem 7.1 and the empty word.** Definition 7.3 says `w ∈ α⁺`, not `α*`.
   Its literal restriction is preserved. Consequently the certificate-generator
   coverage condition cannot hold for a language containing the empty word. The
   fully checked lemma `certificateScheme_excludes_empty_word` establishes this
   directly. Theorem 7.1 itself has no such restriction, while `{ε}` has the
   obvious size-indexed generator. A complete proof of the literal statement will
   require reconciling this discrepancy, such as changing Definition 7.3 to
   include the empty word. This first pass does not silently make that correction.
4. **Certificate composition.** Definition 7.4 does not require *every* sampled
   certificate to certify a length-`n` instance. Definition 7.5 permits an empty
   recovery fibre. Appendix A.20's direct composition argument therefore needs
   additional justification: a sampled certificate with an empty fibre can cause
   recovery to exhaust its input. No extra useful-certificate condition has been
   inserted into `HasCertificateScheme`; this issue remains visible for the proof
   stage.
