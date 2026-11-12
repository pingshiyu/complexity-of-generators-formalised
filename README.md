# Complexity theory of randomised testing — Lean formalisation

Lean 4 proofs about generators, native finite-control machines and their fair-
coin probability semantics. The development follows the current
PLDI27 manuscript. [Current paper status](CURRENT_PAPER_STATUS.md) records the
checked theorems and their model conventions.
The bundled PDF and several retained API names use historical numbering.

The updated expected-time results are fully proved in the native model:

- Proposition 5.2: `PG ⊆ EPG ⊆ NP`.
- Theorem 5.1: infinite `EPG ⊆ ELEPG ⊆ NP`.
- Theorem 5.2 in its stronger form: collision resistance excludes even the raw
  expected-length, expected-polynomial-time model, without fast paths or
  producing-index bounds.
- Theorem 6.1: complement and intersection nonclosure for all three classes;
  the intersection witnesses have infinite intersection.

The polynomial time and space up-to characterisations hold over every finite
alphabet. PG, EPG and current ELEPG are closed under union, concatenation and Kleene
star by actual native constructions. The ELEPG constructions call the original
sources directly, preserving their first moments and global word-length fast paths. The concrete SAT and HAMPATH exact-recursive
constructions and their PG membership theorems are complete. General resource TIME and SPACE containments and up-to characterisations
also hold in the explicit finite multitape model. See the status table for exact model boundaries.

## Definitions and proofs

[ExpectedGenerators.lean](ComplexityOfGenerators/ExpectedGenerators.lean)
separates three notions: exact expected-polynomial-time generation (EPG), raw
expected-length/expected-time generation, and current ELEPG with its global word-length fast-path condition. Moment bounds apply only at nonempty generator indices; the raw
expected-length model requires infinitely many active indices.

[ExpectedGenerationContainment.lean](ComplexityOfGenerators/Proofs/ExpectedGenerationContainment.lean)
proves the EPG containments.
[ExpectedLengthContainment.lean](ComplexityOfGenerators/Proofs/ExpectedLengthContainment.lean)
constructs a native recognizer that guesses a producing index and uses the
global word-length fast path and a derived index bound to prove ELEPG is
contained in NP.
[ELEPGCollision.lean](ComplexityOfGenerators/Proofs/ELEPGCollision.lean)
excludes raw expected-length collision generators by first-moment estimates
and a verified polynomial-time bounded-index search attacker.
[ELEPGBinary.lean](ComplexityOfGenerators/Proofs/ELEPGBinary.lean) and
[ELEPGStar.lean](ComplexityOfGenerators/Proofs/ELEPGStar.lean) prove current ELEPG
closure without imposing layer-local fast paths.
[ExpectedNonclosure.lean](ComplexityOfGenerators/Proofs/ExpectedNonclosure.lean)
updates non-compositionality for the revised classes.

[AcceptingTimeGeneration.lean](ComplexityOfGenerators/Proofs/AcceptingTimeGeneration.lean)
proves that the historical PG trial-budget convention agrees with the current
paper's polynomial accepting-runtime convention. The construction clocks a
native machine and drains randomness on timeout, preserving every output.
[ResourceGeneration.lean](ComplexityOfGenerators/Proofs/ResourceGeneration.lean)
provides a probability-derived full-prefix test and shared recognition criteria.
[UpToGeneration.lean](ComplexityOfGenerators/Proofs/UpToGeneration.lean)
defines actual cumulative-support generator families. The separate
`UpToPolynomialGeneration` and `UpToSpaceGeneration` modules prove both
polynomial characterisations.

[Examples](ComplexityOfGenerators/Examples) contains concrete padded-CNF and
adjacency-matrix HAMPATH semantics, forward/inverse reductions and support
laws, verified parsers, complete word-level self-reductions, certificates and
ancestors. The complete SAT instance is in
[SATNative/ExactRecursive.lean](ComplexityOfGenerators/Examples/SATNative/ExactRecursive.lean):
its verifier, rank, width, reduction, full-support base sampler, and uniform
inverse generator are actual native polynomial machines. HAMPATH's native
polynomial self-reduction, base family, and inverse generator are also checked,
yielding its exact-recursive and PG theorems.
The existing general
[exact-recursive generation theorem](ComplexityOfGenerators/Proofs/ExactRecursiveGeneration.lean)
remains fully proved, including optional stopping after reaching the target
length, empty slices, the empty word and the empty alphabet.

[MainTheorems.lean](ComplexityOfGenerators/MainTheorems.lean) collects the current
PLDI27 results in paper order, including GEN=RE and the SAT/HAMPATH examples.
[HistoricalTheorems.lean](ComplexityOfGenerators/HistoricalTheorems.lean) retains
older numbering, certificate-scheme conventions and the historical PSPACEG
equality. [Definition cross-reference](DEFINITION_CROSS_REFERENCE.md) records model
conventions. Native decision classes are not silently
identified with Complexitylib's classes; individual space translations used by
the proofs are themselves verified.

## Build and audit

Lean and Mathlib are pinned to **v4.34.0**. Direct dependencies are Mathlib,
[Complexitylib](https://github.com/SamuelSchlesinger/complexitylib) at
`d51bfbd39bea4d8a4a3282d4d4ddbb33709ea467`, and
[VCVio](https://github.com/Verified-zkEVM/VCVio) at
`9146f78c4f1bc2c9d8d92da686e9e375315ae5e7`.

```sh
lake update --keep-toolchain
lake exe cache get
lake build
lake env lean scripts/AuditFoundations.lean
python3 scripts/audit-all.py
```

The audit checks every imported local declaration and its transitive axiom
dependencies. Only `propext`, `Classical.choice` and `Quot.sound` are allowed;
`sorryAx`, custom axioms and unchecked evaluation are rejected. Kernel checking
and the axiom audit establish the Lean statements; the correspondence table
separately records which paper claims those statements cover.

The Lake post-update hook applies the recorded Complexitylib cast-proof
compatibility backport; see [patches](patches/README.md). Upstream VCVio may
emit deprecation warnings. No local unfinished-proof warning is expected.

Import individual proof modules for a smaller dependency set. Import
`ComplexityOfGenerators.MainTheorems` for current paper results,
`ComplexityOfGenerators.HistoricalTheorems` for historical aliases, or the root
`ComplexityOfGenerators` module for both. Import
`ComplexityOfGenerators.Foundations` for the complete supporting development.
