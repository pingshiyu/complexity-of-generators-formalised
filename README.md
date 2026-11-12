# Artifact guide: Lean formalisation of generator complexity

This artifact accompanies the current PLDI27 [paper](paper.pdf) on the
complexity of randomised testing. It is a Lean 4 library formalising generators as finite-control
machines, their probability semantics, and the relationship between generation
and decision complexity. It includes concrete machine constructions for SAT
and HAMPATH, expected-time containment and separation results, and closure and
nonclosure results for generator libraries.

The evaluation consists of building the library and checking its theorem
statements and axiom dependencies. No input datasets are required. The sections
below explain how to do this and identify the checked results' correspondence
with the paper.

## 1. Requirements and installation

Use a Unix shell with Bash, Git, curl, Python 3, and `elan`, the Lean toolchain
manager. If Lean is not installed, follow the
[official installation instructions](https://lean-lang.org/install/manual/).
Make sure that `lean` and `lake` are available in your shell. The repository's
[lean-toolchain](lean-toolchain) selects **Lean 4.34.0** automatically through
`elan`.

The dependencies are pinned in [lakefile.lean](lakefile.lean) and
[lake-manifest.json](lake-manifest.json):

| Dependency | Version or revision |
| --- | --- |
| Lean / Mathlib | `v4.34.0` |
| Complexitylib | `d51bfbd39bea4d8a4a3282d4d4ddbb33709ea467` |
| VCVio | `9146f78c4f1bc2c9d8d92da686e9e375315ae5e7` |

Initial setup requires network access to download the toolchain, dependencies,
and Mathlib cache. Run the following commands from the root of this repository:

```sh
lake update --keep-toolchain
lake exe cache get
lake build
```

`lake update` runs the repository's post-update hook, which applies a recorded
upstream compatibility patch to the pinned Complexitylib checkout. The patch
updates four cast proofs for this Lean/Mathlib version; it changes no theorem
statements or definitions. The hook accepts an already applied patch. Details
and the patch itself are in [patches/README.md](patches/README.md).

`lake exe cache get` downloads compiled dependency artifacts, avoiding a full
Mathlib build. `lake build` then compiles the local development and checks its
proofs. A successful build exits with status zero and reports
`Build completed successfully` or `All targets up-to-date`.

To reduce memory pressure, limit the worker threads:

```sh
LEAN_NUM_THREADS=2 lake build
```

Use `LEAN_NUM_THREADS=1` if needed. This Lake version does not accept a
`lake build -j` option. The first build takes longer than subsequent incremental
builds.

## 2. Check the statements and audit the proofs

After the build, run:

```sh
lake env lean scripts/CheckCurrentPaper.lean
lake env lean scripts/AuditFoundations.lean
python3 scripts/audit-all.py
```

The first command imports the current-paper API directly and prints the types
of its principal results and native construction witnesses. It checks the
current certificate, bounded-label, literal collision-language and general-
alphabet theorem types explicitly. It also prints
axiom dependencies for selected results. The second audits every local
declaration in the public import closure. The Python script extends that audit
to **every local Lean source module**, including modules outside that closure.

Both audits permit only Lean's standard logical axioms: `propext`,
`Classical.choice`, and `Quot.sound`. They reject dependencies on `sorryAx`,
custom axioms, or unchecked evaluation. Each audit should exit with status zero
and print a line of the form:

```text
Foundations audit passed: ... local declarations; only propext, Classical.choice and Quot.sound are allowed.
```

The declaration count can change as the development evolves. All commands above
must succeed; the audit success message is additional evidence alongside the
kernel-checked build. Conditional results retain their cryptographic or
complexity-separation assumptions explicitly in their theorem statements.

The retained historical API and space-simulation regressions have additional
checks:

```sh
lake env lean scripts/CheckHistoricalTheorems.lean
lake env lean scripts/CheckSavitchTranslation.lean
```

Lake normally reuses compiled files. To force a rebuild of the local proofs
while retaining dependency caches, run:

```sh
lake clean complexityOfGenerators
lake build
```

Then repeat the statement checks and audits. The argument to `lake clean` is
the package name from `lakefile.lean`; bare `lake clean` also removes dependency
build outputs.

Upstream deprecation and linter warnings may appear during compilation. The
expected Complexitylib “local changes” warning results from the compatibility
patch described above. Build errors and axiom-audit failures require attention.

## 3. Correspondence with the paper

Start with
[MainTheorems.lean](ComplexityOfGenerators/MainTheorems.lean). It collects the
current PLDI27 results in paper order. The table below gives its main entry
points; all names are in the namespace `ComplexityOfGenerators`.

| Current paper result | Lean entry points |
| --- | --- |
| Theorem 3.1: `RE = GEN` | `theorem_3_1_generability_is_recursive_enumerability` |
| Lemma 4.1: acceptance at the time bound | `lemma_4_1_acceptance_at_time_bound` |
| Proposition 4.1: time/space containments | `proposition_4_1_time`, `proposition_4_1_space` |
| Proposition 4.2: up-to resource characterisations | `proposition_4_2_time`, `proposition_4_2_space`; native polynomial specialisations also appear in the file |
| Corollary 5.1: `PG ⊆ NP` | `corollary_5_1_polynomial_generation_subset_np` |
| Proposition 5.1: CNF-SAT in PG | `proposition_5_1_cnf_sat_polynomial_generation` |
| Proposition 5.2: `PG ⊆ EPG ⊆ NP` | `proposition_5_2_expected_polynomial_generation` |
| Theorem 5.1: infinite `EPG ⊆ ELEPG ⊆ NP` | `theorem_5_1_expected_generation_containments` |
| Collision-language membership in P | `observation_collision_language_polynomial_decision` |
| Theorem 5.2: collision non-generability | `theorem_5_2_collision_non_generability`; the stronger `theorem_5_2_raw_expected_length_collision_non_generability` removes the fast-path condition |
| Collision exclusions for PG and EPG | `corollary_5_2_collision_non_generability` |
| Proposition 6.1: certificate schemes characterise PG | `proposition_6_1_generators_are_certificate_schemes` |
| Proposition 6.2: exact-recursive generation implies PG | `proposition_6_2_exact_recursive_generation` |
| SAT and HAMPATH constructions | `example_sat_polynomial_self_reduction`, `example_sat_exact_recursive_generation`, and their `example_hampath_*` counterparts; PG membership is also exposed |
| Proposition 6.3: union, concatenation and Kleene star | Nine `proposition_6_3_*` declarations, one for each operation and each of PG, EPG and ELEPG |
| Theorem 6.1: complement and intersection nonclosure | `theorem_6_1_complement_nonclosure`, `theorem_6_1_infinite_intersection_nonclosure` |

[DEFINITION_CROSS_REFERENCE.md](DEFINITION_CROSS_REFERENCE.md) explains the
formal definitions and model conventions. Important points for interpreting the
table are:

- Most results use the native finite-control machine model. General resource
  containments and characterisations use the explicit finite multitape model.
  Their constructibility, monotonicity and lower-bound hypotheses are visible
  in the Lean statements. Imported Complexitylib classes are not assumed equal
  to the native classes.
- The native evaluator observes terminal states without an extra transition,
  so Lemma 4.1 uses a complete random prefix of `time + 1` bits.
- Theorem 5.1 restricts the EPG-to-ELEPG inclusion to infinite languages.
  Expected length and runtime bounds apply only at nonempty generator indices.
  Current ELEPG uses global word-length fast paths; the separate
  `LayerFastELEPG` definition retains the historical per-layer requirements.
- The stronger raw Theorem 5.2 assumes neither fast paths nor polynomial
  producing-index coverage. Its statement uses the literal separated-pair
  language over `PairSymbol`, as does the polynomial-decision observation. A
  proved native encoding bridge is used internally in the attacker argument.
- SAT uses a concrete padded-CNF encoding. HAMPATH uses loop-free directed
  adjacency matrices: self-loops are excluded, while longer cycles are allowed.
  The current exact-recursive theorem assumes inverse generators only on the
  paper's bounded labels, with accepting-run bounds. Native bounded simulation,
  a width/length postfilter and a general runtime-normalization construction
  derive the internal finite-trial interface. Further encoding
  conventions, including SAT's rank on malformed words, are documented in the
  definition cross-reference.

The certificate-scheme equivalence uses certificates in the instance alphabet,
including the empty word, and quantifies over every certificate. It holds for
every finite alphabet. The nonclosure results use the paper's convention of an
alphabet with at least two symbols (`[Nontrivial α]`). Older positive-binary
certificate and finite-trial interfaces remain available as historical APIs.
Older theorem numbers and aliases live in
[HistoricalTheorems.lean](ComplexityOfGenerators/HistoricalTheorems.lean).
Those aliases explicitly use the numbering of an earlier manuscript;
`paper.pdf` is the current paper.

## 4. Finding and inspecting the proofs

| Location | Contents |
| --- | --- |
| [Machine.lean](ComplexityOfGenerators/Machine.lean), [Generators.lean](ComplexityOfGenerators/Generators.lean) | Native machine execution, halting, generators and generated languages |
| [ComplexityClasses.lean](ComplexityOfGenerators/ComplexityClasses.lean), [ExpectedGenerators.lean](ComplexityOfGenerators/ExpectedGenerators.lean) | Decision/generation classes and expected-time/length definitions |
| [MultitapeModel.lean](ComplexityOfGenerators/MultitapeModel.lean) and related `Multitape*` files | Explicit multitape model and general resource classes |
| [Foundations/](ComplexityOfGenerators/Foundations) | Fair-coin probability, stream semantics and supporting results |
| [Proofs/](ComplexityOfGenerators/Proofs) | Containment, collision, closure and exact-recursive proofs |
| [Simulation/](ComplexityOfGenerators/Simulation) | Concrete native machine constructions and their correctness and cost proofs |
| [Examples/](ComplexityOfGenerators/Examples) | SAT/HAMPATH encodings, reductions, base samplers and inverse generators |
| [scripts/](scripts) | Statement checks, axiom audits and regression checks |

To inspect a result, follow its proof in `MainTheorems.lean` to the underlying
proof module. For example, a small Lean file in the repository root can contain:

```lean
import ComplexityOfGenerators.MainTheorems

open ComplexityOfGenerators

#check theorem_5_1_expected_generation_containments
#check theorem_5_2_raw_expected_length_collision_non_generability
#print axioms proposition_6_3_elepg_star
```

If saved as `Inspect.lean`, run it with `lake env lean Inspect.lean`.
The Lean 4 editor extension also supports inspecting types and navigating to
definitions when the repository is opened as a project.

Import `ComplexityOfGenerators.MainTheorems` for current-paper results,
`ComplexityOfGenerators.HistoricalTheorems` for historical aliases, or the root
`ComplexityOfGenerators` module for both. Individual proof modules can be
imported when a smaller dependency set is sufficient.
