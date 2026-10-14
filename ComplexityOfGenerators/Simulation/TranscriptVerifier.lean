import ComplexityOfGenerators.Simulation.RandomTranscriptCorrectness
import ComplexityOfGenerators.Simulation.GeneratorRecognizerCorrectness
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

/-!
# A native polynomial verifier for the step-transcript certificates

The random-transcript adapter consumes a bit on every source step. The existing
recognizer computes the input length, simulates that adapter at the resulting
index and compares its output with the word. Finally the certificate-reader
compiler moves those random choices onto the auxiliary certificate tape.
Every component starts on blank native tapes and charges for initialization.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

/-- The recognizer's acceptance equivalence only needs source termination on
the chosen finite tape; almost-sure productivity is irrelevant here. -/
theorem generatorRecognizer_accepts_iff_of_halts (word : List α) (bits : BitString)
    (halts : M.Halts (generatorData word.length) bits) :
    (generatorRecognizer M).Accepts (decisionData word) bits ↔
      M.Produces (generatorData word.length) bits word := by
  obtain ⟨t, result, source⟩ := halts
  have target := generatorRecognizer_run M word bits t result source
  constructor
  · rintro ⟨out, time, accepted⟩
    have same := (generatorRecognizer M).halted_outcome_unique _ bits time _ _ _ accepted target
    cases result with
    | accepted output =>
        have equal : output = word := by
          by_contra different
          simp [matcherOutcome, different] at same
        exact ⟨t, by simpa only [equal, transcriptSourceData, generatorData] using source⟩
    | rejected => simp [matcherOutcome] at same
    | exhausted => simp [matcherOutcome] at same
  · rintro ⟨time, accepted⟩
    have same := M.halted_outcome_unique _ bits time _ _ _ accepted source
    subst result
    exact ⟨[], _, by simpa [matcherOutcome] using target⟩

def transcriptVerifierMachine : Machine α Bool Unit :=
  certificateVerifier (generatorRecognizer (randomTranscript M))

theorem transcriptVerifierMachine_deterministic : (transcriptVerifierMachine M).Deterministic :=
  certificateVerifier_deterministic _

def transcriptVerifierTime : PolynomialBound := ⟨100, 2, by decide⟩

theorem transcriptVerifierMachine_timeBound (word : List α) (certificate : BitString) :
    (transcriptVerifierMachine M).TimeBound (verifierData word certificate)
      (transcriptVerifierTime (word.length + certificate.length + 1)) := by
  obtain ⟨result, source, _⟩ := randomTranscript_replay M [] word.length certificate
  have target := generatorRecognizer_run (randomTranscript M) word certificate (2 * certificate.length + 1) result source
  apply Machine.timeBound_mono _ _ _
    (certificateVerifier_timeBound (generatorRecognizer (randomTranscript M)) word certificate _ ⟨_, target⟩)
  simp only [transcriptVerifierTime, PolynomialBound.eval]
  nlinarith

theorem transcriptVerifierMachine_accepts (word : List α) (certificate : BitString) :
    (transcriptVerifierMachine M).Accepts (verifierData word certificate) [] ↔
      (transcriptReplay M).run (generatorData word.length certificate) [] certificate.length =
        .halted (.accepted word) := by
  obtain ⟨result, source, replay⟩ := randomTranscript_replay M [] word.length certificate
  change (certificateVerifier (generatorRecognizer (randomTranscript M))).Accepts _ _ ↔ _
  rw [certificateVerifier_accepts,
    generatorRecognizer_accepts_iff_of_halts (randomTranscript M) word certificate ⟨_, _, source⟩]
  constructor
  · rintro ⟨t, accepted⟩
    have same := (randomTranscript M).halted_outcome_unique _ certificate t _ _ _ accepted source
    subst result
    exact replay
  · intro accepted
    change (transcriptReplay M).run (generatorData word.length certificate) [] certificate.length =
      .halted (certificateOutcome result) at replay
    rw [accepted] at replay
    cases result with
    | accepted output =>
        have equal : word = output := Outcome.accepted.inj (RunState.halted.inj replay)
        exact ⟨_, by simpa only [equal, transcriptSourceData, generatorData] using source⟩
    | rejected => cases replay
    | exhausted => cases replay

end
end ComplexityOfGenerators.Simulation
