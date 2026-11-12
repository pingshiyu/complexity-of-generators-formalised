import ComplexityOfGenerators.Proofs.TranscriptScheme
import ComplexityOfGenerators.Simulation.TranscriptVerifier

/-!
# Polynomial generators yield retained binary certificate schemes

A polynomial generator supplies a concrete native polynomial verifier and
certificate scheme under the historical positive binary certificate and
finite-trial conventions. The verifier, sampler and recoverer are all native
machines with proved costs.

The current Definition 6.1 and Proposition 6.1, with same-alphabet certificates,
empty certificates and accepting-only bounds, are formalised in
`PaperCertificates` and `Proofs.PaperCertificateEquivalence`.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (G : GeneratorFamily α) (seed time : PolynomialBound)
    (bound : G.toUniformGenerators.RunsInTime seed time)

def generatorTranscriptVerifier : PolynomialVerifier G.toUniformGenerators.language where
  machine := transcriptVerifierMachine G.machine
  deterministic := transcriptVerifierMachine_deterministic G.machine
  time := transcriptVerifierTime
  witnessBound := time.add ⟨1, 0, by decide⟩
  timeBound := transcriptVerifierMachine_timeBound G.machine
  complete := by
    intro word member
    have layer : word ∈ G.toUniformGenerators.layer word.length := by
      rw [G.layer_eq_lengthSlice]
      exact ⟨member, rfl⟩
    obtain ⟨certificate, positive, length, recovered⟩ :=
      transcriptRecoverer_bounded_complete G seed time bound word.length word layer
    refine ⟨certificate, positive, ?_, ?_⟩
    · apply length.trans
      simpa [PolynomialBound.eval] using time.add_le ⟨1, 0, by decide⟩ word.length
    · apply (transcriptVerifierMachine_accepts G.machine word certificate).mpr
      rw [transcriptRecoverer_language] at recovered
      exact recovered
  sound := by
    intro word certificate _ accepted
    have replay := (transcriptVerifierMachine_accepts G.machine word certificate).mp accepted
    have recovered : word ∈ (transcriptRecoverer G.machine).generatedLanguage
        (generatorData word.length certificate) := by
      rw [transcriptRecoverer_language]
      exact replay
    exact ⟨word.length, transcriptRecoverer_language_subset G word.length certificate recovered⟩

theorem generatorTranscriptVerifier_verifies :
    VerifiesGeneratorTranscript G (generatorTranscriptVerifier G seed time bound) := by
  intro word certificate _
  exact transcriptVerifierMachine_accepts G.machine word certificate

/-- Native construction of the retained binary certificate scheme from a
polynomial generator, including empty instances and nonempty recovery targets. -/
theorem generatorTranscriptVerifier_hasScheme :
    HasCertificateScheme (generatorTranscriptVerifier G seed time bound) :=
  transcriptScheme_of_verifier G _ (generatorTranscriptVerifier_verifies G seed time bound) ⟨seed, time, bound⟩

theorem pg_has_certificateScheme {L : Language α} (member : L ∈ PG α) :
    ∃ V : PolynomialVerifier L, HasCertificateScheme V := by
  obtain ⟨G, language, seed, time, bound⟩ := member
  subst L
  exact ⟨generatorTranscriptVerifier G seed time bound,
    generatorTranscriptVerifier_hasScheme G seed time bound⟩

end
end ComplexityOfGenerators
