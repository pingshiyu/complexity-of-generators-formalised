import ComplexityOfGenerators.Proofs.TranscriptScheme
import ComplexityOfGenerators.Simulation.TranscriptVerifier

/-!
# The forward implication of Theorem 7.1

A polynomial generator supplies a concrete native polynomial verifier and a
certificate scheme for that same verifier. Neither the verifier nor either
component of the scheme is an assumed simulation interface.
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

/-- Complete native construction of the certificate scheme from a polynomial
generator, preserving empty words and the nonempty recovery requirement. -/
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
