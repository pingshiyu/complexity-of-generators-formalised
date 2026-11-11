# Paper definitions and their Lean implementations

This guide connects the definitions in [Complexity Theory of Randomised Testing](complexity-of-generators-formalisation.pdf) to the Lean declarations used by the main theorems. It is intended for a manual comparison: each entry identifies the paper passage, the implementation, and the conditions to check. It also covers Appendix A.23 and lists numbered definitions without a direct implementation.

**The correspondence is not uniformly literal.** In particular, the formalisation changes the time-bound convention, corrects the collision-language index, and changes two certificate conditions. The machine model and some encodings also differ. These points are separated from changes of representation for which the repository supplies an equivalence proof.

The source snapshot is commit `8aa1087507532f8498cf8bd215d93f3ff6228af1`. Declaration links below point to that commit on GitHub, at the relevant source line. Paper page numbers use the printed `0:n` numbering; in this PDF they also equal the one-based PDF page numbers. All Lean names are in `ComplexityOfGenerators` unless another namespace is stated.

For local browsing, the principal files are [Machine.lean](ComplexityOfGenerators/Machine.lean), [Generators.lean](ComplexityOfGenerators/Generators.lean), [ComplexityClasses.lean](ComplexityOfGenerators/ComplexityClasses.lean), [Cryptography.lean](ComplexityOfGenerators/Cryptography.lean), [Certificates.lean](ComplexityOfGenerators/Certificates.lean), [SelfReducibility.lean](ComplexityOfGenerators/SelfReducibility.lean), and [MainTheorems.lean](ComplexityOfGenerators/MainTheorems.lean).

## Reading the correspondence

The following descriptions distinguish the kinds of correspondence:

- **Direct in the native model:** the mathematical conditions are recorded using the repository's machine and encoding conventions.
- **Proved representation change:** the source presents the same object differently and supplies a relevant equivalence lemma.
- **Revised:** a condition differs from the printed definition.
- **Specialised or partial:** only a restricted case or part of the paper definition is represented.
- **No direct counterpart:** the numbered definition is not implemented as such. Related infrastructure is identified where useful.

“Direct” does not itself assert a proved equivalence between the native machine model and every tape convention in the paper.

The basic notation is:

| Paper notation | Lean representation | What to check |
| --- | --- | --- |
| A finite word over an alphabet, `Σ*` | [Word α][word], an abbreviation for `List α` | The empty word is `[]`. Language classes generally assume `[Fintype α]`; the empty alphabet is allowed. |
| Positive words, `Σ+` | A word together with a condition such as `w ≠ []` | There is no separate positive-word type. Check where the nonemptiness condition is actually imposed. |
| Finite random bits, `{0,1}*` | [BitString][bitstring] = `List Bool` | The empty seed exists and is included in finite-run termination requirements. |
| Infinite random bits, `{0,1}ω` | [BitStream][bitstream] = `ℕ → Bool` | Stream events are measured with `fairCoinMeasure`. |
| A language and a class of languages | [Language α][language-type] = `Set (Word α)`; [LanguageClass α][language-class] = `Set (Language α)` | Membership is a proposition, without a supplied decision procedure. |
| `L_n = {w ∈ L : length(w) = n}` | [lengthSlice L n][length-slice] | Size zero is included; this means exact length, not length at most `n`. |

## Transducers and probability

### Definitions 2.1 to 2.3

Paper: [0:4–0:5](complexity-of-generators-formalisation.pdf#page=4), including the tape preliminaries.

| Paper definition | Lean implementation | Correspondence and manual check |
| --- | --- | --- |
| **2.1 Bitstring transducer**, 0:5 | [Machine][machine], [Instruction][instruction], [Configuration][configuration], [Machine.Produces][produces] | **Direct in the native model, with tape differences below.** A finite transition table drives a work tape, random input, and output. `Produces data b w` means that some finite run ends with `.accepted w`; merely writing `w` before rejection does not produce it. |
| **2.2 Random selection**, 0:5 | [Instruction.readRandom][read-random], [Machine.next][next] | **Specialised operational representation.** Each `readRandom` consumes exactly one bit and chooses one of two next states. Random reads and ordinary work/output steps are separate instructions. |
| **2.3 Halting transducer**, 0:5 | [Machine.HaltingTransducer][halting-transducer], [Machine.Halts][halts], [Machine.observe][observe], [Outcome][outcome] | **Direct in the native model.** Every finite seed, including `[]`, must halt. The predicate forbids the explicit `.rejected` outcome on every seed and clock. Attempting to read beyond the seed automatically produces `.exhausted`, which represents the paper's permitted rejection. |

The model details worth checking against the preliminaries are:

- **Tapes and heads.** The paper takes tapes to be right-infinite. Lean's work tape is indexed by `ℤ`, with a two-way head. Ordinary, auxiliary, and unary-index inputs have separate read-only tapes. Their heads are [clamped][input-move] to the input and its first right blank cell, so blank input positions cannot be used as unbounded counters.
- **Finite control.** The transition table sees the control state and current ordinary, auxiliary, index, and work symbols. It cannot inspect an entire input, the accumulated output, or a head coordinate. States and work symbols are `Fin` types. The index is stored as a natural number in [InputData][input-data], but the machine sees only the current unary mark or blank.
- **Blank symbols and output.** Work cells contain `Option (Fin M.symbols)`, with `none` for blank. `Instruction.step` can leave a cell unchanged or write a nonblank symbol; it cannot write a blank, consistent with the paper's prohibition. Output is an append-only list: emitting adds one symbol, and blank output cells are not represented.
- **Time and space.** [Machine.run][run] counts primitive nonterminal instructions. Acceptance, explicit rejection, and exhaustion are observed without an additional step. [Machine.SpaceBound][space-bound] counts distinct visited work cells, including the initial cell and a cell entered immediately before termination. Input, random, and output storage is not charged.

These are concrete conventions to approve as part of the comparison. The repository does not supply a blanket equivalence theorem identifying this entire model with the paper's tape conventions; the specific library comparisons are discussed below.

### Definitions 2.4 to 2.9

Paper: [0:5–0:6](complexity-of-generators-formalisation.pdf#page=5).

| Paper definition | Lean implementation | Correspondence and manual check |
| --- | --- | --- |
| **2.4 Minimal accepted bitstrings `A_T`**, 0:5 | [Machine.MinimalAcceptedSeed][minimal-seed] | `M.Accepts data b ∧ ∀ k < b.length, ¬ M.Accepts data (b.take k)`. The paper says every strict prefix *rejects*; under `HaltingTransducer`, nonacceptance is exhaustion because divergence and explicit rejection are excluded. The empty minimal seed is permitted. |
| **2.5 Evaluation on infinite streams**, 0:6 | [Machine.acceptedStreams][accepted-streams], together with [Machine.Produces][produces] on finite prefixes | **Partial.** The repository represents the event that some finite prefix accepts. It does not define a separate output-valued partial function `T(bs)` with a divergence case. Do not read `acceptedStreams` as that function. |
| **2.6 Fair independent bitstreams**, 0:6 | [fairCoinMeasure][fair-measure] | **Direct.** `Measure.infinitePi` of the uniform Boolean measure, indexed by `ℕ`. It is the specified fair-coin product measure, not an arbitrary probability measure. |
| **2.7 Cylinder `S_b`**, 0:6 | [cylinder][cylinder] | **Direct.** The set of streams agreeing with `b` at every index below its length. The mass formula is proved in [fairCoinMeasure_cylinder][cylinder-mass]. |
| **2.8 Accepted infinite streams `A_T^ω`**, 0:6 | [Machine.acceptedStreams][accepted-streams] | **Proved representation change.** Lean takes the union of cylinders over all accepting seeds, rather than only minimal accepting seeds. [Machine.acceptedStreams_eq_minimal_prefixes][minimal-equivalence] proves equality with the paper's event. [Machine.measurableSet_acceptedStreams][acceptance-measurable] proves measurability. |
| **2.9 Generator**, 0:6 | [Machine.IsGenerator][is-generator] | **Direct in the native model.** Requires `HaltingTransducer` and acceptance measure equal to **one or zero**. It does not require termination on every infinite stream, nor a uniform output distribution. |

Two supporting facts help check the semantics:

- [Machine.produces_append][produces-append] preserves an accepted output under extension of its seed, implementing Observation 2.1.
- [Machine.generator_probability_one_iff_nonempty][productive-iff] proves that a generator has acceptance probability one exactly when its generated language is nonempty. The measure-zero alternative therefore represents the empty language, not a nonempty language of zero-probability outputs.

**Definition 2.10, generator by rejection sampling**, [0:7](complexity-of-generators-formalisation.pdf#page=7), has no direct generic constructor matching the printed procedure. The recognition-to-generation proof uses its own bounded-recognition and fallback construction; that construction should not be mistaken for an implementation of Definition 2.10.

## Generated languages and uniform families

### Definitions 3.1 to 3.4

| Paper definition | Lean implementation | Correspondence and manual check |
| --- | --- | --- |
| **3.1 Generated language `L(G)`**, [0:9](complexity-of-generators-formalisation.pdf#page=9) | [Machine.generatedLanguage][generated-language] | **Direct.** `w` is in the language iff some **nonempty** finite seed produces it. This is support, not an output probability bound. The nonempty-seed convention agrees with the displayed paper definition. A machine accepting on the empty seed still has its output included, because an accepted seed can be extended. |
| **3.2 `GEN`**, [0:9](complexity-of-generators-formalisation.pdf#page=9) | [GEN][gen] | **Direct in the native model.** There exists one `Machine Unit Bool α`, a proof it is a generator at `generatorData 0`, and equality of its generated language with `L`. No resource bound is imposed. |
| **3.3 `RE`**, [0:10](complexity-of-generators-formalisation.pdf#page=10) | [RE][re] | **Direct in the native model, with a proved library comparison.** A deterministic machine accepts `w` on the empty choice tape iff `w ∈ L`. There is no requirement to terminate off the language. [native_RE_iff_rePred][re-agreement] connects this class with Mathlib's `REPred`, under the encoding assumptions in that file. |
| **3.4 `HALT`**, [0:11](complexity-of-generators-formalisation.pdf#page=11) | No direct word-language declaration for the paper's encoded pairs `⟨M,w⟩` | Related results [ComputabilityFoundation.halting_recursively_enumerable][halting-re] and [ComputabilityFoundation.halting_undecidable][halting-undecidable] concern Mathlib partial-recursive codes at a fixed input. They are not a definition of the paper's exact pair-encoded `HALT` language. |

### Definitions 4.1 and 4.2

Paper: [0:12](complexity-of-generators-formalisation.pdf#page=12).

| Paper definition | Lean implementation | Correspondence and manual check |
| --- | --- | --- |
| **4.1 Implementation of a uniform family** | [UniformGenerators][uniform-generators], [generatorData][generator-data] | **Specialised.** One finite machine is shared by every natural-number index, supplied in unary on a read-only tape. There is no arbitrary function choosing a different machine at each index. The general paper index set `C ⊆ {0,1}*` is not represented as a general family interface. |
| **4.2 Family of generators and its language** | [UniformGenerators.layer][layer], [UniformGenerators.language][family-language], [GeneratorFamily][generator-family] | **Specialised to the length partition for generation classes.** `layer n` is the support at index `n`; `language` is the union of layers. `GeneratorFamily.outputLength` requires every output of layer `n` to have length exactly `n`. |

`UniformGenerators` alone does **not** constrain output length or require disjoint layers. Certificate samplers and Appendix A.23 base samplers need that more general interface. `PG`, `GTIME`, `GSPACE`, and `PSPACEG` require the stricter `GeneratorFamily`. The connection between a family layer and the corresponding length slice of its whole language is proved in [GeneratorFamily.layer_eq_lengthSlice][layer-slice].

## Time and space bounds

### Definitions 4.3 and 5.1 and Remark 1

Paper: [0:12–0:13](complexity-of-generators-formalisation.pdf#page=12). This is a **revised convention**, not a literal transcription.

The paper's Definition 4.3 says that `G_n` terminates within `t(n)`; Definition 5.1 uses a polynomial bound. Remark 1 then tests emptiness using a seed whose length is that same time bound. In the native operational model, an empty generator must consume every supplied finite seed before exhausting, so a bound independent of arbitrary seed length cannot hold on all seeds.

The implementation [Machine.GeneratorTimeBound][generator-time] takes **two** budgets:

```lean
(∀ b, b.length ≤ seedBudget → M.HaltsWithin data b timeBudget) ∧
(∀ b, b.length = seedBudget →
  (M.Accepts data b ↔ (M.generatedLanguage data).Nonempty))
```

Thus:

1. Every trial with at most the seed budget halts within the execution budget.
2. Every full-budget seed accepts when the generated language is nonempty.
3. Every full-budget seed exhausts when the language is empty, provided the machine is a generator.

The third fact is [bounded_trial_exhausted_iff_empty][empty-trial]. No direct bound on arbitrary-length seeds is imposed; for empty slices, longer seeds can take longer to exhaust. For nonempty slices, acceptance of every full-budget seed and preservation under extension also bound runs on longer seeds. The two budgets permit setup and simulation work without increasing the amount of randomness an empty generator must consume.

| Paper object | Lean implementation | Exact scope |
| --- | --- | --- |
| **4.3 Time-bounded family** | [UniformGenerators.RunsInTime][runs-time] | `∀ n, GeneratorTimeBound (generatorData n) (seed n) (time n)`. Both budget functions are explicit arguments. |
| **4.3 `GTIME(t)`** | [GTIME][gtime] | Exists an exact-length family with language `L`, and **some positive seed function** with `RunsInTime seed t`. The seed function is not required to be polynomial or constructible. The supplied `t : ℕ → ℕ` need not be time-constructible. |
| **5.1 Polynomial-time family** | [UniformGenerators.PolynomialTime][polynomial-time] | `∃ seed time : PolynomialBound, RunsInTime seed time`. Both are uniform polynomial bounds for the whole family. |
| **5.2 `PG`** | [PG][pg] | Exists an exact-length family with language `L` and `PolynomialTime`. The paper writes a union of `GTIME(n^i)`; Lean directly quantifies polynomial budgets and does not define `PG` by that union. |

The one-step-overhead example [delayedEmptyGenerator_not_generatorTimeBound][delayed-empty] shows why forcing the *same numerical value* for both budgets is problematic in this native model. It does not prove equivalence between the revised convention and the paper's literal wording.

### Polynomial conventions

[PolynomialBound][polynomial-bound] consists of a positive natural coefficient `c` and natural exponent `k`, evaluated as `c * (n + 1)^k`. Bounds hold at every size, including zero. [BivariatePolynomialBound][bivariate-bound] evaluates as `c * (n + m + 1)^k`.

[PolynomialBound.asPolynomial_eval][as-polynomial] identifies the univariate expression with a Mathlib polynomial, and [PolynomialBound.eval_le_ofPolynomial][polynomial-domination] proves domination of every natural-coefficient polynomial. These support the use of this bound format. They are not a theorem equating the complete class definitions with the paper's asymptotic notation or its literal unions over powers `n^i`.

### Definitions 4.4 and 6.2

| Paper object | Lean implementation | Correspondence and manual check |
| --- | --- | --- |
| **4.4 Space-bounded family**, [0:12](complexity-of-generators-formalisation.pdf#page=12) | [Machine.SpaceBound][space-bound], [UniformGenerators.RunsInSpace][runs-space] | **Direct work-space condition in the native model.** Bounds visited work cells on all finite seeds and at all clocks, including terminal successors. It does not bound runtime or charge random/output tapes. |
| **4.4 `GSPACE(s)`**, 0:12 | [GSPACE][gspace] | **Extended parameter domain.** Exists an exact-length family with language `L` and the stated space bound. Lean allows any `s : ℕ → ℕ`; the paper restricts to space-constructible functions. Constructibility is not a field. |
| **6.2 `PSPACEG`**, [0:18](complexity-of-generators-formalisation.pdf#page=18) | [UniformGenerators.PolynomialSpace][polynomial-space], [PSPACEG][pspaceg] | Exists an exact-length family and a `PolynomialBound` on work space. The paper expresses this as a union over `GSPACE(n^i)`. The same polynomial-format qualification applies. |

**Definitions 5.6–5.7 (`EPG`) and 6.1 (`LG`) are not formalised as generation classes.** In particular, `PolynomialTime` is not an expected-time condition. An imported decision class named `Standard.L` is not the paper's generator class `LG`.

## Collision resistance

Paper: [Definitions 5.3–5.5, 0:15](complexity-of-generators-formalisation.pdf#page=15).

### Definition 5.3

[HashFunction][hash-function] contains:

| Paper requirement | Lean field or declaration | Check |
| --- | --- | --- |
| `h_n : {0,1}^{n+1} → {0,1}^n` | `hash : (n : ℕ) → Bits (n + 1) → Bits n`; [Bits][bits] = `Fin n → Bool` | Domain and codomain lengths are enforced by the type. At `n = 0`, the output is empty. This also resolves the paper's conflicting general codomain notation `{0,1}+` at that boundary. |
| One uniform efficient implementation | `implementation`, `deterministic`, `computes`, `timeBound` | A single deterministic native machine computes every valid `h_n`, with the unary index and input word on separate tapes. Its polynomial bound depends on `n`. |
| Computation on the intended hash domain | `computes` and `timeBound` quantify `x : Bits (n + 1)` | Behaviour on inputs of other lengths is not specified. The paper also writes an ambient function on all positive strings; that ambient off-domain behaviour is not part of this Lean structure. |

### Definition 5.4

The relevant declarations are [CollisionFinder][collision-finder], [collisionSuccess][collision-success], [HashFunction.CollisionResistant][collision-resistant], and [CollisionResistantHashFunctionsExist][hash-exists].

The resistance condition is:

```lean
¬ ∃ A : CollisionFinder, ∃ q : PolynomialBound,
  Set.Infinite { n : ℕ |
    (q n : ℝ≥0∞)⁻¹ < fairCoinMeasure (collisionSuccess h A n) }
```

Check the quantifiers in this order: no **single uniform** polynomial-time attacker and no **single polynomial threshold** achieve strictly greater than inverse-polynomial success at infinitely many parameters. The strict inequality and the “infinitely many” quantifier are preserved.

An attacker is a general randomised algorithm, not an `IsGenerator`: it may explicitly reject or produce an incorrect candidate. Its [ordinary TimeBound][time-bound] applies to **all** finite seeds. Success requires an accepted output encoding two genuinely distinct, correctly sized preimages with equal hashes. Randomness uses the same fair-coin measure as generators. The assumption remains unkeyed and uniform; it does not add a key distribution or nonuniform circuits.

The optional library comparison [HashFunction.collisionResistant_iff_vcvio][vcvio-equivalence] connects this exact condition to a VCVio security game with the same attacker type. It is not a replacement of the native definition by a different cryptographic assumption.

### Definition 5.5

**The hash index is corrected.** The printed definition applies `h_|x|` to `x`, although Definition 5.3 gives that function a domain of words of length `|x| + 1`. Lean's [HashFunction.IsCollision][is-collision] instead quantifies `a b : Bits (n + 1)` and checks `a ≠ b ∧ h.hash n a = h.hash n b`.

The collision languages are explicit encodings of this corrected predicate:

| Declaration | Representation |
| --- | --- |
| [encodePair][encode-pair] | `x`, then a reserved `PairSymbol.separator`, then `y`. |
| [HashFunction.collisionLanguage][collision-language] | All `encodePair x y` for which `h.IsCollision n x y` holds for some `n`. A collision at parameter `n` occupies length `2 * (n + 1) + 1`. |
| [pairSymbolBits][pair-symbol-bits] and [binaryPairWord][binary-pair-word] | Fixed two-bit encoding: bit zero becomes `00`, bit one becomes `01`, and the separator becomes `10`. |
| [HashFunction.binaryCollisionLanguage][binary-collision-language] | The binary language actually used in the separation proof. Parameter `n` occupies length `4 * (n + 1) + 2`, as recorded in [HashFunction.binary_collision_slice_nonempty][binary-collision-slice]. Malformed encodings are excluded. |

The parameter `n`, preimage length `n + 1`, and encoded word length are different quantities. This correction also changes the size arithmetic in the paper's collision-generation argument.

## Certificate schemes

Paper: [Definitions 7.2–7.6, 0:23–0:24](complexity-of-generators-formalisation.pdf#page=23).

### Definition 7.2

[PolynomialVerifier L][polynomial-verifier] packages the verifier and its proofs:

| Paper condition | Lean field | Manual check |
| --- | --- | --- |
| Input `w#c`, with a positive certificate | `machine : Machine α Bool Unit`, using [verifierData][verifier-data] | Certificates are **binary**; words use `α`. Word and certificate occupy separate read-only tapes rather than a separator-coded tape. Positive certificates are expressed by `c ≠ []`. |
| Deterministic polynomial-time verification | `deterministic`, `time`, `timeBound` | The time bound is `time (w.length + c.length + 1)` and holds for all `w,c`, including empty certificates. |
| Completeness with bounded certificates | `witnessBound`, `complete` | For every `w ∈ L`, there is a **nonempty** certificate of length at most `witnessBound w.length` that is accepted. |
| Soundness | `sound` | Acceptance implies `w ∈ L` for **every positive certificate**, not only certificates below `witnessBound`. Soundness imposes no condition on `c = []`. |

The paper uses the same alphabet `Σ` for words and certificates. Binary certificates and separate input tapes are modelling choices here; this file does not prove an alphabet/tape encoding equivalence. In particular, the usual binary encoding intuition should not silently be applied to the empty or unary alphabet.

### Definition 7.3

**Revised.** The paper defines certified inputs using `w ∈ Σ+`. Lean's [PolynomialVerifier.certifiedInputs][certified-inputs] is:

```lean
{ w | c ≠ [] ∧ V.machine.Accepts (verifierData w c) [] }
```

It allows the **empty instance word** while still excluding the empty certificate. Thus `V.certifiedInputs [] = ∅`, but `[]` may belong to `V.certifiedInputs c` for positive `c`.

This change matters to Theorem 7.1: [empty_word_language_in_pg][empty-word-pg] constructs a `PG` generator for `{ε}`, whereas [literal_certificate_coverage_characterization_false][literal-counterexample] shows failure of the corresponding characterization with the original positive-instance coverage restriction. [LiteralCertificateCoverage][literal-coverage] retains that restriction for the counterexample; it is not the certificate-scheme definition used by the theorem.

### Definition 7.4

[CertificateGenerator V][certificate-generator] has these fields:

| Paper condition | Lean field | Manual check |
| --- | --- | --- |
| A uniform certificate generator at each requested instance length | `sampler : UniformGenerators Bool` | Certificate length need not equal the requested instance length. This intentionally uses `UniformGenerators`, not `GeneratorFamily`. |
| Polynomial runtime | `polynomialTime` | Uses the separate seed and execution budgets described above. |
| Coverage of exactly the length-`n` slice | `covers` | `lengthSlice L n = {w \| w.length = n ∧ ∃ c, c ∈ sampler.layer n ∧ w ∈ V.certifiedInputs c}`. This is equality, not just soundness or one inclusion. |
| Reject on an empty slice | `rejectsEmpty` | If the slice is empty, the sampler accepts no finite seed. Its generator property ensures rejection is by exhaustion. |
| **Additional condition, absent from the paper** | `certifiesInstance` | Every certificate in `sampler.layer n` must certify **at least one instance of length `n`**. |

The last condition is a substantive strengthening. The printed coverage equation alone permits extra sampled certificates with no certified instance at the requested length. Such a certificate would give the recoverer an empty language. The additional field excludes that case when composing sampler and recoverer; [CertificateRecoverer.sampled_trial_accepts][sampled-trial] proves acceptance of every full recovery trial arising from a sampled certificate.

### Definitions 7.5 and 7.6

| Paper definition | Lean implementation | Correspondence and manual check |
| --- | --- | --- |
| **7.5 Certificate recovery** | [CertificateRecoverer V][certificate-recoverer] | One `Machine Unit Bool α` handles all `(n,c)`. For **every positive certificate**, `isGenerator` requires a genuine generator, `recovers` equates its language to `lengthSlice L n ∩ V.certifiedInputs c`, and `timeBound` supplies separate bivariate seed/time bounds. The polynomial parameters are `n` and `c.length`. |
| **7.6 Certificate scheme** | [HasCertificateScheme V][certificate-scheme] | `Nonempty (CertificateGenerator V) ∧ Nonempty (CertificateRecoverer V)`. Both components refer to the **same verifier**. This incorporates the revised Definitions 7.3–7.4 and the revised time convention. |

The recovery requirement is not restricted to certificates the sampler emits, or to polynomially bounded certificate lengths. An arbitrary positive certificate may have an empty recovery fibre, in which case recovery is an empty generator. The nonempty-fibre guarantee applies specifically to sampled certificates.

## Self reducibility and exact recursive generation

Paper: [Appendix A.23, 0:45–0:49](complexity-of-generators-formalisation.pdf#page=45). These definitions support Proposition A.23.2 in addition to the five main theorems.

### Definition A.23.1

The definition is split into [SelfReduction L][self-reduction] for the semantic conditions and [PolynomialSelfReduction R][polynomial-self-reduction] for actual computational witnesses. **`SelfReduction L` alone does not assert polynomial computability.**

| Paper notation or clause | Lean implementation | Manual check |
| --- | --- | --- |
| Certificate set `C(x)` | `SelfReduction.certificates` and `certifies` | `x ∈ L ↔ (certificates x).Nonempty`. Certificates here are `Word α`, and may be empty. This is a separate certificate convention from Section 7. |
| Certificate length `l(x)` | `rank`, `certificate_length` | Every certificate of `x` has length exactly `rank x`. The rank is defined on all words, including nonmembers. |
| Polynomial bound on `l(x)` | `rankBound`, `rank_le` | An everywhere bound of the form `c * (length(x) + 1)^k`. |
| Prefix length `σ(x)` | `width`, `positive` | `0 < rank x ↔ 0 < width x`. |
| `σ(x) = O(log length(x))` | `logCoefficient`, `logConstant`, `width_le` | Explicit bound `width x ≤ a * Nat.log 2 (x.length + 1) + b`, including small and empty inputs. |
| Reduction `ψ(x,w)` | `reduce` | A total function on two words; computational implementation is required separately. |
| Length nonincrease | `length_reduce` | For **all** `x,w`, `length(reduce x w) ≤ length(x)`, not only labels of the intended width. |
| Rank decrease | `rank_reduce` | For **all** `x,w`, `rank (reduce x w) ≤ rank x - width x`. Natural subtraction implements truncation at zero. |
| Certificate decomposition, Equation (1) | `split` | `c ∈ C(x)` iff there are `w,d` with `length(w) = width x`, `d ∈ C(reduce x w)`, and `c = w ++ d`. The equation also applies at rank zero. |
| Polynomial verifier | `PolynomialSelfReduction.verifier`, `verifier_deterministic`, `verifier_time`, `verifier_correct` | A native deterministic machine decides the entire relation `c ∈ C(x)`, including `c = []`. This also supplies the zero-certificate test in item (2). |
| Polynomial computation of `l`, `σ`, and `ψ` | `rank_computable`, `width_computable`, `reduction_computable`, using [PolynomialWordFunction][polynomial-word-function] | Each function has an actual deterministic native transducer and a time bound in the combined input lengths. Natural-valued outputs are encoded in unary as lists of `Unit`. |

The appendix explicitly uses empty certificates at rank zero, whereas Definition 7.2 requires positive certificates. Lean makes that change of convention explicit rather than reusing `PolynomialVerifier`. The explicit polynomial and logarithmic bounds also replace the paper's asymptotic notation; no general equivalence theorem for all these conventions is supplied here.

### Definitions A.23.2 and A.23.4

| Paper definition | Lean implementation | Correspondence and manual check |
| --- | --- | --- |
| **A.23.2 Iterated reduction `ψ*`**, 0:45 | [SelfReduction.Iterated][iterated] | **Relational representation of a partial computation.** `Iterated x w y` records that consuming label word `w` reduces `x` to `y`. `single` handles exactly one width-sized label; `more` composes with a **nonempty remaining suffix**. It is not a total Lean function returning a word. |
| Positive reduction steps used in proofs | [SelfReduction.Step][reduction-step], [SelfReduction.Path][reduction-path] | `Step` explicitly requires positive width; `Path` is its reflexive transitive closure. These are supporting definitions, not extra hypotheses of A.23.1. They avoid treating zero-width calls as rank-decreasing steps. |
| **A.23.4 Ancestor set `A_n`**, 0:47 | [SelfReduction.ancestors][ancestors] | Requires `y ∈ L` and either `y.length = n` or a length-`n` member `x` with a **nonempty** label word `w` and `Iterated x w y`. This preserves the paper's `Σ+` condition on the iterated label. |

The paper's recursive clauses for `ψ*` overlap unless the recursive case is read as having a remaining suffix; zero-width calls also need care. Inspect the `Iterated` constructors when checking that interpretation. [SelfReduction.mem_ancestors_iff][ancestor-path-equivalence] proves the equivalent presentation using positive-step paths.

### Definition A.23.5

[ExactRecursiveGenerators R][exact-recursive-generators] supplies the two uniform generator components:

| Paper component | Lean fields | Manual check |
| --- | --- | --- |
| Base family `Λ_n^L` | `base`, `baseTime`, `base_language`, with [SelfReduction.bases][bases] | `base.layer n = {y ∈ R.ancestors n : R.rank y = 0}`. Outputs need not have length exactly `n`, so this is `UniformGenerators α`. |
| Inverse fibre `Ψ_{n,y,w}` | [SelfReduction.inverseFibre][inverse-fibre] | Exactly `{x ∈ R.ancestors n : R.reduce x w = y ∧ w.length = R.width x}`. Empty labels are retained in this definition. |
| Uniform inverse generator | `inverse : Machine α α α`, `inverse_generator`, `inverse_language` | One machine handles all parameters: ordinary input `y`, auxiliary input `w`, and unary index `n`. Requirements quantify all `n,w` and all `y ∈ L`, not just ancestor values encountered by a particular run. |
| Polynomial inverse runtime | `inverseSeed`, `inverseTime`, `inverse_time` | Both trial bounds depend **only on `n`**, as in the paper's stated parameter bound, not on `length(y) + length(w)`. Empty fibres use the revised exhaustion convention. |

[ExactlyRecursivelyGenerable L][exactly-recursive] then means:

```lean
∃ R : SelfReduction L, Nonempty (PolynomialSelfReduction R) ∧
  Nonempty (ExactRecursiveGenerators R)
```

It does not include `L ∈ PG` as a field or an assumed compiler.

Two nearby proof corrections should be kept distinct from this definition:

- **Proposition A.23.2 stopping rule.** The printed algorithm stops at the first word of length `n`, although reductions may preserve length. The helper theorems [printed_algorithm_misses_member][printed-stop-failure] and [optional_stop_covers_member][optional-stop], both in `SelfReduction.StoppingExample`, exhibit a missed word and a successful continuation. The implemented construction permits stopping or continuing at length `n` and uses nonempty inverse labels to force rank progress. This changes the construction, not the stated target of `inverseFibre`.
- **Lemma A.23.2 membership premise.** The paper's proof assumes `x ∈ L`, omitted from its statement. [SelfReduction.exists_base_path][base-path] explicitly requires that premise when establishing a path to a rank-zero member.

**Definition A.23.3, recursive generability without an exact requested size, has no direct counterpart.** It should not be identified with `ExactlyRecursivelyGenerable`, whose hypotheses are different.

## Decision classes and closure used by the theorems

The main theorem declarations use the **native** definitions below. These are not aliases of imported library classes.

| Concept | Lean declaration | Exact condition to inspect |
| --- | --- | --- |
| `P` | [P][p] | Exists a deterministic native machine and a polynomial `TimeBound` on every input, accepting exactly the language. |
| `NP` | [NP][np] | Exists a native machine and a polynomial time bound on **all finite choice tapes**; `w ∈ L` iff **some** tape leads to acceptance. There is no probability threshold. |
| `coNP` | [coNP][conp] | `L ∈ coNP α` iff `Lᶜ ∈ NP α`. Complement is relative to all finite words, including malformed encodings. |
| `PSPACE` | [PSPACE][pspace] | Exists a deterministic machine that halts on every input, has a polynomial visited-work-cell bound, and accepts exactly the language. |
| Closure under complement | [ClosedUnderComplement][closed-complement] | `∀ L, L ∈ C → Lᶜ ∈ C`. |
| Closure under binary intersection | [ClosedUnderIntersection][closed-intersection] | `∀ L K, L ∈ C → K ∈ C → L ∩ K ∈ C`. |

The imported aliases [Standard.P, Standard.NP, Standard.PSPACE, and related classes][standard-classes] live in a different namespace. [DecisionClassAgreement][class-agreement] states full comparison obligations but is not supplied as a proved instance. Specific machine translations, including [standard_pspace_subset_pspace][standard-space-inclusion] and [standard_pspace_encoded_preimage][standard-space-preimage], are proved and used in [pspaceg_subset_pspace][generator-space-inclusion]. This should not be read as an established equality of all native and imported time/space classes. In contrast, the native `RE` comparison cited above is proved.

For Theorem 7.2, closure is a property of sets of languages. It does not assert or deny the existence of a compiler for a particular predicate syntax.

## Remaining numbered definitions

These entries complete the inventory of numbered definitions in the paper. “No direct counterpart” does not rule out reusable general-purpose library machinery; it means that machinery is not a formalisation of the identified paper definition.

| Paper definition and location | Status in this repository |
| --- | --- |
| **5.6 Expected polynomial-time family**, [0:16](complexity-of-generators-formalisation.pdf#page=16) | No direct counterpart for either the expected-runtime bound or the additional requirement that every supported word have some polynomially bounded producing run. |
| **5.7 `EPG`**, 0:16 | No direct counterpart. |
| **5.8 `PRIMES`**, [0:17](complexity-of-generators-formalisation.pdf#page=17) | No direct counterpart for this binary-encoded prime language used in the expected-time discussion. |
| **6.1 `LG`**, [0:18](complexity-of-generators-formalisation.pdf#page=18) | No direct generator-class declaration. Arbitrary-function `GSPACE` is available but is not a separate formalisation of this definition. |
| **6.3 Directed graph `REACH`**, [0:19](complexity-of-generators-formalisation.pdf#page=19) | No direct declaration of the paper's graph-encoded language. Machine-configuration reachability machinery serves a different purpose. |
| **6.4 Function-oracle TM**, [0:20](complexity-of-generators-formalisation.pdf#page=20) | No direct counterpart. The native instruction type has no oracle instruction. |
| **6.5 Length-bounded oracle function**, 0:20 | No direct counterpart in the paper's oracle framework. |
| **6.6 Oracle space classes**, [0:21](complexity-of-generators-formalisation.pdf#page=21) | No direct counterpart for the relativised generation and decision classes. |
| **6.7 Oracle polynomial-space classes**, 0:21 | No direct counterpart. Theorem 6.1 is unrelativised. |
| **7.1 `DEFAULT(L)`**, [0:22](complexity-of-generators-formalisation.pdf#page=22) | No direct class of default-element functions. Specific fallback generators do not implement this general definition or its `FP` characterization. |
| **A.1.1 Extensible transducer**, [0:30](complexity-of-generators-formalisation.pdf#page=30) | No direct predicate for the alternative extension-based productivity notion. `IsGenerator` uses the measure-based notion. |
| **A.2.1 `s(b)` and A.2.2 `e(b)`**, [0:31](complexity-of-generators-formalisation.pdf#page=31) | No direct implementations of these named extension-set and selected-extension functions. Seed-extension lemmas elsewhere do not define these objects. |
| **A.11.1 Configuration of `H`**, [0:37](complexity-of-generators-formalisation.pdf#page=37) | **Related machinery, not the same definition.** [Configuration][configuration] is the full native runtime record; [Machine.DecisionView][decision-view] and [Machine.SpaceCode][space-code] support bounded configuration reasoning. They do not define the paper's exact DFA-node tuple or its `LG` construction. |
| **A.11.2 Writing transition**, 0:37 | **Related operational representation.** `Instruction.step` has an optional emitted symbol, and [Machine.next][next] appends it. There is no separate predicate implementing the paper's writing transitions on the constructed DFA. |
| **A.11.3 Output of an execution path**, [0:38](complexity-of-generators-formalisation.pdf#page=38) | **Related operational representation.** `Configuration.output` accumulates symbols in execution order and `Produces` observes accepted output. There is no separate function on the paper's DFA paths. |
| **A.12.1 Relation image and domain**, 0:38 | No dedicated correspondence for these objects in the paper's sampling construction. |
| **A.12.2 Logspace transducer for a relation**, [0:39](complexity-of-generators-formalisation.pdf#page=39) | No direct counterpart. |

Definitions 2.10, 3.4, and A.23.3 are covered in their respective sections above.

## Where the main statements use these definitions

| Paper result | Lean theorem | Definitions to inspect together |
| --- | --- | --- |
| **Theorem 3.1**, [0:10](complexity-of-generators-formalisation.pdf#page=10) | [theorem_3_1_generability_is_recursive_enumerability][theorem-3-1] | `RE α = GEN α`; Definitions 2.1–2.9 and 3.1–3.3, with the native recogniser model. |
| **Theorem 5.1**, [0:15](complexity-of-generators-formalisation.pdf#page=15) | [theorem_5_1_cryptographic_separation][theorem-5-1] | `CollisionResistantHashFunctionsExist → PG Bool ⊂ NP Bool ∧ ¬ P Bool ⊆ PG Bool`; Definitions 4.1–4.3 and 5.1–5.4, plus the corrected binary collision language used by the proof. |
| **Theorem 6.1**, [0:22](complexity-of-generators-formalisation.pdf#page=22) | [theorem_6_1_polynomial_space_generation][theorem-6-1] | `PSPACEG α = PSPACE α`; Definitions 4.1–4.2, 4.4, and 6.2, with native visited-cell space accounting. |
| **Theorem 7.1**, [0:24](complexity-of-generators-formalisation.pdf#page=24) | [theorem_7_1_generators_are_certificate_schemes][theorem-7-1] | `L ∈ PG α ↔ ∃ V : PolynomialVerifier L, HasCertificateScheme V`; the revised time convention and revised Definitions 7.3–7.4 are part of this statement. `L ∈ NP` is not an extra hypothesis. |
| **Theorem 7.2**, [0:25](complexity-of-generators-formalisation.pdf#page=25) | [theorem_7_2_efficient_generators_are_not_composable][theorem-7-2] | Two independent implications: `NP Bool ≠ coNP Bool` rules out complement closure of `PG Bool`; existence of collision-resistant hashes rules out intersection closure. |
| **Proposition A.23.2**, [0:47–0:49](complexity-of-generators-formalisation.pdf#page=47) | [proposition_a23_2_exact_recursive_generation][proposition-a23-2] | `ExactlyRecursivelyGenerable L → L ∈ PG α`; A.23.1, A.23.2, A.23.4, and A.23.5, with the corrected construction discussed above. |

## Manual review checklist

- [ ] Accept the native tape, head, transition-cost, and visited-cell conventions as the intended interpretation of the paper's machine model.
- [ ] Check the proved minimal-prefix/event equivalence and the distinction between accepted-stream events and an output-valued stream evaluator.
- [ ] Check unary uniformity, exact-length slices, and the inclusion of size zero and empty alphabets.
- [ ] Approve the separate seed/execution budgets as a revision of the printed time convention; distinguish `GTIME`'s arbitrary seed function from `PG`'s polynomial seed bound.
- [ ] Check everywhere polynomial bounds and the omission of constructibility from general `GTIME` and `GSPACE`.
- [ ] Approve the corrected hash index, valid-input scope, and pair encodings; check the strict inverse-polynomial inequality on infinitely many parameters.
- [ ] Approve binary positive certificates, empty certified instances, and the additional requirement that every sampled certificate has a nonempty recovery fibre at the requested length.
- [ ] Check the appendix's separate empty-certificate convention, computational witnesses, partial iterated-reduction relation, and uniform inverse bounds.
- [ ] Distinguish native decision classes from imported `Standard` aliases, and note which comparisons are proved.
- [ ] Check that the definitions listed as absent are outside the scope you intend to certify.

[word]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L27
[bitstring]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L25
[bitstream]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L26
[language-type]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L28
[language-class]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L29
[length-slice]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L78
[machine]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L56
[instruction]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L46
[configuration]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L72
[produces]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L166
[read-random]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L50
[next]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L123
[halting-transducer]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L25
[halts]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L163
[observe]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L113
[outcome]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L84
[input-move]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L41
[input-data]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L66
[run]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L152
[space-bound]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L185
[minimal-seed]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/GeneratorSupport.lean#L86
[accepted-streams]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L31
[fair-measure]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L12
[cylinder]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L16
[cylinder-mass]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/Probability.lean#L76
[minimal-equivalence]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/GeneratorSupport.lean#L108
[acceptance-measurable]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/Probability.lean#L97
[is-generator]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L35
[produces-append]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/RandomTape.lean#L190
[productive-iff]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/GeneratorSupport.lean#L69
[generated-language]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L42
[gen]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L50
[re]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L91
[re-agreement]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/GenerabilityContainment.lean#L37
[halting-re]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/Computability.lean#L34
[halting-undecidable]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/Computability.lean#L39
[uniform-generators]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L57
[generator-data]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L212
[layer]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L65
[family-language]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L68
[generator-family]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Generators.lean#L74
[layer-slice]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/BoundedGeneration.lean#L74
[generator-time]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L30
[empty-trial]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L40
[runs-time]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L71
[gtime]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L124
[polynomial-time]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L76
[pg]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L137
[delayed-empty]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/EmptyTrialOverhead.lean#L87
[polynomial-bound]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L19
[bivariate-bound]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L58
[as-polynomial]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/ResourceBounds.lean#L20
[polynomial-domination]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/ResourceBounds.lean#L34
[runs-space]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L80
[gspace]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L132
[polynomial-space]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L83
[pspaceg]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L142
[hash-function]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L21
[bits]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L16
[collision-finder]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L46
[collision-success]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L53
[collision-resistant]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L62
[hash-exists]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L67
[time-bound]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L180
[vcvio-equivalence]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/Cryptography.lean#L193
[is-collision]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L32
[encode-pair]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Cryptography.lean#L41
[collision-language]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/Cryptography.lean#L41
[pair-symbol-bits]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/BinaryCollisions.lean#L15
[binary-pair-word]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/BinaryCollisions.lean#L19
[binary-collision-language]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/BinaryCollisions.lean#L75
[binary-collision-slice]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/BinaryCollisions.lean#L88
[polynomial-verifier]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L24
[verifier-data]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Machine.lean#L220
[certified-inputs]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L40
[empty-word-pg]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/EmptyWordGeneration.lean#L123
[literal-counterexample]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/EmptyWordGeneration.lean#L151
[literal-coverage]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L104
[certificate-generator]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L75
[sampled-trial]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L167
[certificate-recoverer]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L88
[certificate-scheme]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Certificates.lean#L99
[self-reduction]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L31
[polynomial-self-reduction]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L53
[polynomial-word-function]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L21
[iterated]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L82
[reduction-step]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L73
[reduction-path]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L77
[ancestors]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L89
[ancestor-path-equivalence]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/SelfReduction.lean#L125
[exact-recursive-generators]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L107
[bases]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L94
[inverse-fibre]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L98
[exactly-recursive]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/SelfReducibility.lean#L126
[printed-stop-failure]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/ExactRecursiveStopping.lean#L96
[optional-stop]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/ExactRecursiveStopping.lean#L107
[base-path]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/SelfReduction.lean#L57
[p]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L96
[np]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L104
[conp]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L110
[pspace]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/ComplexityClasses.lean#L114
[closed-complement]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/LanguageClosure.lean#L8
[closed-intersection]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/LanguageClosure.lean#L12
[standard-classes]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/Classical.lean#L22
[class-agreement]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/ModelBridge.lean#L27
[standard-space-inclusion]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/LibrarySpace.lean#L9
[standard-space-preimage]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/LibrarySpace.lean#L19
[generator-space-inclusion]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Proofs/PolynomialSpaceBase.lean#L17
[decision-view]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/SpaceConfigurations.lean#L22
[space-code]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/Foundations/SpaceConfigurations.lean#L85
[theorem-3-1]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/MainTheorems.lean#L40
[theorem-5-1]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/MainTheorems.lean#L50
[theorem-6-1]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/MainTheorems.lean#L65
[theorem-7-1]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/MainTheorems.lean#L78
[theorem-7-2]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/MainTheorems.lean#L91
[proposition-a23-2]: https://github.com/pingshiyu/complexity-of-generators-formalised/blob/8aa1087507532f8498cf8bd215d93f3ff6228af1/ComplexityOfGenerators/MainTheorems.lean#L101
