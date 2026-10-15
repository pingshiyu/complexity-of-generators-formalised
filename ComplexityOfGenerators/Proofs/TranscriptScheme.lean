import ComplexityOfGenerators.Proofs.TranscriptSampling

/-!
# Assembling the forward certificate scheme from a replay verifier

The sampler and recoverer below are the concrete native machines, with all
scheme obligations proved. The explicit verifier premise is correctness
of a polynomial verifier for this specific replay relation. An arbitrary NP
verifier does not suffice: both components must use the same certificates.
`PolynomialCertificateSchemes` constructs the verifier and discharges this premise.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (G : GeneratorFamily α)
    (V : PolynomialVerifier G.toUniformGenerators.language)

/-- Specification discharged by the native verifier compiler: on `(word,c)`,
replay the source with unary index `word.length` and compare its entire output
with `word`. The verifier must satisfy this for every positive certificate. -/
def VerifiesGeneratorTranscript : Prop :=
  ∀ word c, c ≠ [] →
    (V.machine.Accepts (verifierData word c) [] ↔
      (transcriptReplay G.machine).run (generatorData word.length c) [] c.length =
        .halted (.accepted word))

variable (verifies : VerifiesGeneratorTranscript G V)
include verifies

/-- Correct replay verification identifies the recovery language for every
certificate and index, including invalid certificates and size zero. -/
theorem transcriptRecoverer_certified (n : ℕ) (c : BitString) (positive : c ≠ []) :
    (transcriptRecoverer G.machine).generatedLanguage (generatorData n c) =
      lengthSlice G.toUniformGenerators.language n ∩ V.certifiedInputs c := by
  ext word
  constructor
  · intro recovered
    have length := transcriptRecoverer_outputs_length G n c word recovered
    have member := transcriptRecoverer_language_subset G n c recovered
    rw [G.layer_eq_lengthSlice n] at member
    refine ⟨member, positive, ?_⟩
    apply (verifies word c positive).mpr
    rw [length]
    exact (Set.ext_iff.mp (transcriptRecoverer_language G.machine n c) word).mp recovered
  · rintro ⟨member, certified⟩
    rw [transcriptRecoverer_language]
    have replay := (verifies word c positive).mp certified.2
    simpa only [Set.mem_ofPred_eq, member.2] using replay

def transcriptCertificateRecoverer : CertificateRecoverer V where
  machine := transcriptRecoverer G.machine
  seed := ⟨1, 0, by decide⟩
  time := ⟨1, 1, by decide⟩
  isGenerator := fun n c _ => transcriptRecoverer_isGenerator G.machine n c
  recovers := transcriptRecoverer_certified G V verifies
  timeBound := by
    intro n c _
    apply Machine.TrialBound.mono_time _ (transcriptRecoverer_trialBound G.machine n c)
    simp [BivariatePolynomialBound.eval]

variable (polynomial : G.toUniformGenerators.PolynomialTime)
include polynomial

def transcriptCertificateGenerator : CertificateGenerator V where
  sampler := transcriptUniformSampler G.toUniformGenerators
  polynomialTime := transcriptUniformSampler_polynomial G.toUniformGenerators polynomial
  covers := by
    intro n
    ext word
    constructor
    · intro member
      have source := member
      rw [← G.layer_eq_lengthSlice n] at source
      obtain ⟨certificate, sampled, recovered⟩ := transcriptSampler_covers G n word source
      have positive := (transcriptSampler_recovers_instance G n certificate sampled).1
      rw [transcriptRecoverer_certified G V verifies n certificate positive] at recovered
      exact ⟨member.2, certificate, sampled, recovered.2⟩
    · rintro ⟨length, certificate, _, certified⟩
      exact ⟨V.certifiedInputs_subset certificate certified, length⟩
  certifiesInstance := by
    intro n certificate sampled
    obtain ⟨positive, word, _, recovered⟩ := transcriptSampler_recovers_instance G n certificate sampled
    exact ⟨word, by
      rw [← transcriptRecoverer_certified G V verifies n certificate positive]
      exact recovered⟩
  rejectsEmpty := by
    intro n empty bits accepted
    obtain ⟨certificate, produced⟩ := accepted
    have sampled : certificate ∈ (transcriptUniformSampler G.toUniformGenerators).layer n :=
      ⟨bits ++ [false], by simp,
        (transcriptSampler G.machine).produces_append (generatorData n) bits [false] certificate produced⟩
    obtain ⟨_, word, _, recovered⟩ := transcriptSampler_recovers_instance G n certificate sampled
    have member := transcriptRecoverer_language_subset G n certificate recovered
    rw [G.layer_eq_lengthSlice n, empty] at member
    exact member

/-- The constructive forward direction is reduced to the stated verifier
compiler obligation, without assuming any generator or composition primitive. -/
theorem transcriptScheme_of_verifier : HasCertificateScheme V :=
  ⟨⟨transcriptCertificateGenerator G V verifies polynomial⟩,
    ⟨transcriptCertificateRecoverer G V verifies⟩⟩

end
end ComplexityOfGenerators
