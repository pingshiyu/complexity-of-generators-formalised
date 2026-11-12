import ComplexityOfGenerators.ComplexityClasses

/-!
# Retained binary certificate schemes

This file keeps the historical interface: certificates are positive binary
strings, and sampler and recoverer costs use finite-trial budgets. Empty
instance words are allowed. Every sampled certificate certifies an instance
of the requested length, ensuring a nonempty recovery target.

The current paper's Definition 6.1 is formalised in `PaperCertificates`:
certificates use the instance alphabet, include the empty word, and the
runtime premises constrain accepting runs only. The full current Proposition
6.1 is proved in `Proofs.PaperCertificateEquivalence`.
-/

namespace ComplexityOfGenerators

variable {α : Type} (L : Language α)

/-- The retained verifier requires soundness for all positive binary
certificates, including those beyond the completeness witness bound. -/
structure PolynomialVerifier where
  machine : Machine α Bool Unit
  deterministic : machine.Deterministic
  time : PolynomialBound
  witnessBound : PolynomialBound
  timeBound : ∀ w c, machine.TimeBound (verifierData w c) (time (w.length + c.length + 1))
  complete : ∀ w, w ∈ L → ∃ c : BitString,
    c ≠ [] ∧ c.length ≤ witnessBound w.length ∧ machine.Accepts (verifierData w c) []
  sound : ∀ w c, c ≠ [] → machine.Accepts (verifierData w c) [] → w ∈ L

namespace PolynomialVerifier

variable {L}

/-- Certified inputs in the retained interface may be empty instance
words; the certificate itself must be a positive binary word. -/
def certifiedInputs (V : PolynomialVerifier L) (c : BitString) : Language α :=
  { w | c ≠ [] ∧ V.machine.Accepts (verifierData w c) [] }

theorem certifiedInputs_subset (V : PolynomialVerifier L) (c : BitString) :
    V.certifiedInputs c ⊆ L := fun w h => V.sound w c h.1 h.2

theorem mem_iff_bounded_certificate (V : PolynomialVerifier L) (w : Word α) :
    w ∈ L ↔ ∃ c, c.length ≤ V.witnessBound w.length ∧ w ∈ V.certifiedInputs c := by
  constructor
  · intro member
    obtain ⟨c, positive, length, accepted⟩ := V.complete w member
    exact ⟨c, length, positive, accepted⟩
  · rintro ⟨c, _, certified⟩
    exact V.certifiedInputs_subset c certified

end PolynomialVerifier

/-- A cofinal family of polynomial bounds in the two parameters `n` and `|c|`. -/
structure BivariatePolynomialBound where
  coefficient : ℕ
  degree : ℕ
  coefficient_pos : 0 < coefficient

def BivariatePolynomialBound.eval (p : BivariatePolynomialBound) (n m : ℕ) : ℕ :=
  p.coefficient * (n + m + 1) ^ p.degree

instance : CoeFun BivariatePolynomialBound (fun _ => ℕ → ℕ → ℕ) :=
  ⟨BivariatePolynomialBound.eval⟩

variable {L}

/-- The retained sampler emits certificates whose lengths can differ
from the index. Coverage is over length-`n` instances, and every emitted
certificate certifies at least one such instance. Costs use trial budgets. -/
structure CertificateGenerator (V : PolynomialVerifier L) where
  sampler : UniformGenerators Bool
  polynomialTime : sampler.PolynomialTime
  covers : ∀ n, lengthSlice L n =
    { w | w.length = n ∧ ∃ c, c ∈ sampler.layer n ∧ w ∈ V.certifiedInputs c }
  certifiesInstance : ∀ n c, c ∈ sampler.layer n →
    (lengthSlice L n ∩ V.certifiedInputs c).Nonempty
  rejectsEmpty : ∀ n, lengthSlice L n = ∅ →
    ∀ b, ¬ sampler.machine.Accepts (generatorData n) b

/-- The retained recoverer handles all `(n,c)` with positive binary `c`,
including empty recovery targets. Seed and execution budgets are polynomial
in the index and certificate length. -/
structure CertificateRecoverer (V : PolynomialVerifier L) where
  machine : Machine Unit Bool α
  seed : BivariatePolynomialBound
  time : BivariatePolynomialBound
  isGenerator : ∀ n c, c ≠ [] → machine.IsGenerator (generatorData n c)
  recovers : ∀ n c, c ≠ [] → machine.generatedLanguage (generatorData n c) =
    lengthSlice L n ∩ V.certifiedInputs c
  timeBound : ∀ n c, c ≠ [] →
    machine.GeneratorTimeBound (generatorData n c) (seed n c.length) (time n c.length)

/-- A certificate scheme in the retained interface consists of sampler
and recoverer components for the same verifier. -/
def HasCertificateScheme (V : PolynomialVerifier L) : Prop :=
  Nonempty (CertificateGenerator V) ∧ Nonempty (CertificateRecoverer V)

/-- An earlier coverage clause additionally excluded empty instance words.
It is retained to state its empty-word obstruction and is not a condition of
`HasCertificateScheme`. -/
def LiteralCertificateCoverage (V : PolynomialVerifier L) : Prop :=
  ∃ sampler : UniformGenerators Bool, ∀ n, lengthSlice L n =
    {w | w.length = n ∧ ∃ c, c ∈ sampler.layer n ∧ w ≠ [] ∧ w ∈ V.certifiedInputs c}

theorem literal_certificate_coverage_excludes_empty_word (V : PolynomialVerifier L)
    (coverage : LiteralCertificateCoverage V) : [] ∉ L := by
  obtain ⟨sampler, covers⟩ := coverage
  intro h
  have member : ([] : Word α) ∈ lengthSlice L 0 := ⟨h, rfl⟩
  rw [covers 0] at member
  obtain ⟨_, c, _, certified⟩ := member
  exact certified.1 rfl

/-- The sampler's nonempty-recovery condition makes every emitted
certificate positive in the retained binary interface. -/
theorem CertificateGenerator.certificate_nonempty {V : PolynomialVerifier L}
    (S : CertificateGenerator V) (n : ℕ) (c : BitString) (sampled : c ∈ S.sampler.layer n) :
    c ≠ [] := by
  obtain ⟨w, _, certified⟩ := S.certifiesInstance n c sampled
  exact certified.1

theorem CertificateGenerator.sampler_nonempty_iff {V : PolynomialVerifier L}
    (S : CertificateGenerator V) (n : ℕ) :
    (S.sampler.layer n).Nonempty ↔ (lengthSlice L n).Nonempty := by
  constructor
  · rintro ⟨c, sampled⟩
    obtain ⟨w, member, _⟩ := S.certifiesInstance n c sampled
    exact ⟨w, member⟩
  · rintro ⟨w, member⟩
    rw [S.covers n] at member
    obtain ⟨_, c, sampled, _⟩ := member
    exact ⟨c, sampled⟩

/-- The language-level equation needed by sampler/recoverer composition. The
native sequential compiler is supplied by `Simulation.SamplerComposition` and
used in `Proofs.CertificateSchemeGeneration`. -/
theorem CertificateRecoverer.sampled_union_eq {V : PolynomialVerifier L}
    (R : CertificateRecoverer V) (S : CertificateGenerator V) (n : ℕ) :
    {w | ∃ c, c ∈ S.sampler.layer n ∧ w ∈ R.machine.generatedLanguage (generatorData n c)} =
      lengthSlice L n := by
  ext w
  constructor
  · rintro ⟨c, sampled, recovered⟩
    rw [R.recovers n c (S.certificate_nonempty n c sampled)] at recovered
    exact recovered.1
  · intro member
    have covered := member
    rw [S.covers n] at covered
    obtain ⟨_, c, sampled, certified⟩ := covered
    refine ⟨c, sampled, ?_⟩
    rw [R.recovers n c (S.certificate_nonempty n c sampled)]
    exact ⟨member, certified⟩

/-- Every recovery call arising from this sampler has a nonempty language.
Arbitrary certificates may still have empty recovery languages. -/
theorem CertificateRecoverer.sampled_language_nonempty {V : PolynomialVerifier L}
    (R : CertificateRecoverer V) (S : CertificateGenerator V) (n : ℕ) (c : BitString)
    (sampled : c ∈ S.sampler.layer n) :
    (R.machine.generatedLanguage (generatorData n c)).Nonempty := by
  rw [R.recovers n c (S.certificate_nonempty n c sampled)]
  exact S.certifiesInstance n c sampled

/-- A full recovery trial accepts for every certificate emitted by this
sampler, since each such certificate has a nonempty recovery target. -/
theorem CertificateRecoverer.sampled_trial_accepts {V : PolynomialVerifier L}
    (R : CertificateRecoverer V) (S : CertificateGenerator V) (n : ℕ) (c : BitString)
    (sampled : c ∈ S.sampler.layer n) (bits : BitString)
    (length : bits.length = R.seed n c.length) :
    R.machine.Accepts (generatorData n c) bits := by
  apply ((R.timeBound n c (S.certificate_nonempty n c sampled)).2 bits length).2
  exact R.sampled_language_nonempty S n c sampled

end ComplexityOfGenerators
