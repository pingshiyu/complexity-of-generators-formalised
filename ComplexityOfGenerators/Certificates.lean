import ComplexityOfGenerators.ComplexityClasses

/-!
# Certificate schemes (Definitions 7.2–7.6)

Certificates are binary strings. This is an explicit encoding choice; changing
between fixed finite alphabets with at least two symbols has constant-factor cost.
The two read-only input tapes represent the paper's separator-encoded `w#c`.

The **literal** nonempty-word restriction `w ∈ α⁺` in Definition 7.3 is retained
in `certifiedInputs`. It has a consequence for Theorem 7.1 at length zero; see
`certificateScheme_excludes_empty_word` and the correspondence notes in README.
No extra hypothesis excluding the empty word is silently added to the theorem.
-/

namespace ComplexityOfGenerators

variable {α : Type} (L : Language α)

/-- Definition 7.2, including soundness for *all* positive certificates, not only
the bounded certificates used to witness completeness. -/
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

/-- Definition 7.3, literally `V_f(c) = { w ∈ α⁺ | V(w#c) accepts }`.
The certificate itself must also be positive, as stipulated in Definition 7.2. -/
def certifiedInputs (V : PolynomialVerifier L) (c : BitString) : Language α :=
  { w | w ≠ [] ∧ c ≠ [] ∧ V.machine.Accepts (verifierData w c) [] }

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

/-- Definition 7.4. The sampler's outputs are certificates, so their length is
not forced to equal the index. Coverage is restricted to length-`n` instances. -/
structure CertificateGenerator (V : PolynomialVerifier L) where
  sampler : UniformGenerators Bool
  polynomialTime : sampler.PolynomialTime
  covers : ∀ n, lengthSlice L n =
    { w | w.length = n ∧ ∃ c, c ∈ sampler.layer n ∧ w ∈ V.certifiedInputs c }
  rejectsEmpty : ∀ n, lengthSlice L n = ∅ →
    ∀ b, ¬ sampler.machine.Accepts (generatorData n) b

/-- Definition 7.5. One machine handles all `(n,c)`; its time bound is polynomial
in both parameters. The recovery condition holds for every positive certificate,
including certificates which certify no instance of the requested length. -/
structure CertificateRecoverer (V : PolynomialVerifier L) where
  machine : Machine Unit Bool α
  time : BivariatePolynomialBound
  isGenerator : ∀ n c, c ≠ [] → machine.IsGenerator (generatorData n c)
  recovers : ∀ n c, c ≠ [] → machine.generatedLanguage (generatorData n c) =
    lengthSlice L n ∩ V.certifiedInputs c
  timeBound : ∀ n c, c ≠ [] →
    machine.GeneratorTimeBound (generatorData n c) (time n c.length)

/-- Definition 7.6: existence of both components for the *same* verifier. -/
def HasCertificateScheme (V : PolynomialVerifier L) : Prop :=
  Nonempty (CertificateGenerator V) ∧ Nonempty (CertificateRecoverer V)

/-- A checked consequence of the literal `α⁺` in Definition 7.3.
This exposes the paper's length-zero issue without changing its theorem statement. -/
theorem certificateScheme_excludes_empty_word (V : PolynomialVerifier L)
    (scheme : HasCertificateScheme V) : [] ∉ L := by
  obtain ⟨S⟩ := scheme.1
  intro h
  have member : ([] : Word α) ∈ lengthSlice L 0 := ⟨h, rfl⟩
  rw [S.covers 0] at member
  obtain ⟨_, c, _, certified⟩ := member
  exact certified.1 rfl

end ComplexityOfGenerators
