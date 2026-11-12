# Current PLDI27 correspondence

This file compares the Lean sources with the PLDI27 manuscript in
`../complexity-of-randomised-testing/PLDI27`, as examined on 12 November 2026.
The bundled PDF and historical theorem entry points use older numbering.
A compiled helper or semantic construction is not counted as a compiled native
generator for the whole paper result.

| Current paper result | Checked result | Remaining obligation |
| --- | --- | --- |
| Proposition 4.1, general time/space containments | Complete TIME and SPACE containments in the explicit finite multitape model, with charged constructors, configuration clocks, matching and binary index simulation | None in this model |
| Proposition 4.2, up-to resource characterisations | Complete general TIME and SPACE equalities under the paper’s constructibility, monotonicity and lower-bound hypotheses; native polynomial specialisations over every finite alphabet | None in these models |
| Proposition 5.2, `PG ⊆ EPG ⊆ NP` | Complete: `proposition_5_2_expected_polynomial_generation` | None in the native model |
| Theorem 5.1, infinite `EPG ⊆ ELEPG ⊆ NP` | Complete: `theorem_5_1_expected_generation_containments` | None in the native model |
| Theorem 5.2, collision non-generability | Complete in the stronger raw form: `theorem_5_2_raw_expected_length_collision_non_generability` | None in the native binary collision encoding |
| Proposition 6.3, positive closure of all three classes | Complete native PG/EPG/ELEPG union, concatenation and Kleene star; current ELEPG uses original-source calls and global word-length fast paths | None in the native model |
| SAT exact-recursive construction | Complete: `PaddedCNF.polynomialSelfReduction`, `PaddedCNF.exactlyRecursivelyGenerable`, and `PaddedCNF.language_mem_pg`, using the native base/inverse machines | None for the concrete padded-CNF encoding |
| HAMPATH exact-recursive construction | Complete: `HAMPATH.polynomialSelfReduction`, `HAMPATH.exactlyRecursivelyGenerable`, and `HAMPATH.language_mem_pg`, using the native base/inverse machines | None for the concrete loop-free directed adjacency-matrix encoding |

All rows above have checked public theorem entry points, subject to the stated
model conventions. No construction is supplied by an axiom, `sorry`, assumed
compiler, or a structure field that simply asks for the desired conclusion.

## Definitions repaired

`UniformGenerators.activeIndices` is the set of indices with nonempty output
language. `ExpectedLength` and `RawExpectedPolynomialTime` are constrained only
there. `ExpectedLengthExpectedPolynomialTime` requires infinitely many such
indices and contains no fast-path condition. `ELEPG` additionally requires a
polynomial-in-word-length accepting path at some index for every generated
word. Unary-index locality derives a polynomial producing-index bound while
preserving that same fast run. The older per-layer fast-path definition is
retained explicitly as `LayerFastELEPG`; it is not used in place of the current
definition. `EPG` retains
exact lengths and short accepting paths, and includes finite languages.

The collision proof uses only raw first moments on an arbitrary infinite set
of active indices. It does not assume that every sufficiently large index is
active. The native bounded-index attacker is constructed and its polynomial
runtime is proved. No variance, independence between runtime and length,
short-path condition, or producing-index coverage is used.

`GTIME` now bounds only accepting executions, as in the current paper.
`GTIMEUpTo` and `GSPACEUpTo` use actual cumulative families.
`mem_pg_iff_exists_gtime_polynomial` and
`mem_pg_iff_accepting_polynomial_time` prove agreement of the historical PG
trial-budget convention with accepting-execution polynomial time. It constructs
an actual clocked, rejection-draining generator. The native evaluator observes
acceptance without a further transition, so a safe complete prefix has
`time + 1` bits; this is stated explicitly in the operational lemmas.

## Additional updated results

Current Theorem 6.1 now has checked complement and infinite-intersection
nonclosure for PG, EPG and ELEPG. These results use the revised definitions.
Historical GEN=RE, certificate-scheme equivalence, general exact-recursive
implies PG, and PSPACEG=PSPACE proofs remain available.

## Refactoring and compilation

- One native matcher correctness lemma and one polynomial witness criterion
  replace separate exact, cumulative and expected-time containment arguments.
- One polynomial-space layer criterion replaces duplicated exact/cumulative
  Savitch translation proofs.
- The old eventual-index collision lemmas are special cases of the new
  infinite-index argument.
- The unused `ModelBridge` specifications were removed. Their unfilled SAT and
  class-equality fields were never proved model comparisons.
- Shared bounded-source and input routines replace duplicate exact-recursive
  setup/simulation proofs (the three affected modules fall from 305 to 152 lines).
  Fresh leaf elaboration with shared cached dependencies, median of three runs
  on the same machine: Trial 10.98→2.77 s, TrialBounds 4.77→3.02 s, Prepare
  10.26→2.76 s (combined 26.02→8.55 s). This measures these leaves, not a clean
  whole-repository build. Reproduce with `scripts/benchmark-refactor.py`; raw
  results are in `benchmarks/bounded-source-refactor.json`.
- A shared fixed-consumption finite-scan proof handles seed traces for both
  concatenation and star; the Boolean block codec is shared by HAMPATH labels
  and rational choice.
- The superseded binary up-to sampler was replaced by one finite-alphabet
  sampler, including the empty-alphabet case.
- New example modules import only the tactics they use.
- `Foundations` and `Proofs` still expose historical machinery for compatibility;
  use the individual theorem modules when a smaller import is sufficient.

The retained single-work-tape compiler has quadratic overhead in the simulated
execution length. This suffices for bounded polynomial computations. It does
not preserve an arbitrary expected-time bound using first moments alone, and
it does not establish a general `O(t)` multitape characterisation. The checked EPG and layer-fast closure constructions use bounded independent
phases and checked geometric second moments. Current ELEPG closure instead
uses original source calls whose simulation overhead is linear in their
runtime; all three closure constructions are checked.
`ExpectedNormalisation` and `BoundedPhaseFamilies` implement the balanced phases
used by union and concatenation. For star, `CertifiedStarPhase` checks active
indices and selects a feasible positive composition. `ExpectedStarGenerator`
executes the actual outer retry and sequential factor calls in one finite
native machine. `ExpectedStarSampleTrace` relates its finite runs to the fair
stream sampler; `ExpectedStarSampleCost` and `ExpectedStarNativeProperties`
prove the mean and expected runtime bounds. `ExpectedStar` packages the EPG and
`LayerFastELEPG` closure theorems. The current ELEPG source-call development
retains original first moments, with a moving unary-index packet and direct
output; the complete closure theorems are `elepg_union`, `elepg_concatenation` and
`elepg_star`. Their native execution, finite halting, full support, first-moment
bounds and global word-length fast paths are proved.
