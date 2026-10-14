import ComplexityOfGenerators.Simulation.RejectDrain
import ComplexityOfGenerators.Simulation.TranscriptReplay
import ComplexityOfGenerators.Proofs.GeneratorCriteria
import ComplexityOfGenerators.Foundations.BoundedGeneration

/-!
# Total deterministic computations as singleton-or-empty generators

Explicit rejection is converted to exhaustion by the proved native compiler.
The result generates exactly the deterministic output, if any, and otherwise
the empty language. A seed budget `s` requires at most the deterministic running
time plus `s` steps. Applying this to transcript replay gives a recoverer with
linear certificate-length cost, before identifying its language with a verifier.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

variable {I A O : Type} (M : Machine I A O) (deterministic : M.Deterministic)
    (data : InputData I A) (t : ℕ) (result : Outcome O)
    (source : M.run data [] t = .halted result)

include deterministic source

theorem rejectDrain_deterministic_run (bits : BitString) :
    (rejectDrain M).run data bits (t + bits.length) = .halted (rejectDrainOutcome result) :=
  rejectDrain_run_halted M data bits t result
    ((M.deterministic_run deterministic data bits [] t).trans source)

theorem rejectDrain_accepts_iff (bits : BitString) :
    (rejectDrain M).Accepts data bits ↔ ∃ word, result = .accepted word := by
  have halted := rejectDrain_deterministic_run M deterministic data t result source bits
  cases result with
  | accepted word =>
      constructor
      · intro _
        exact ⟨word, rfl⟩
      · intro _
        exact ⟨word, t + bits.length, halted⟩
  | rejected =>
      constructor
      · rintro ⟨word, time, accepted⟩
        have impossible := (rejectDrain M).halted_outcome_unique data bits time _ _ _ accepted halted
        cases impossible
      · rintro ⟨word, impossible⟩
        cases impossible
  | exhausted =>
      constructor
      · rintro ⟨word, time, accepted⟩
        have impossible := (rejectDrain M).halted_outcome_unique data bits time _ _ _ accepted halted
        cases impossible
      · rintro ⟨word, impossible⟩
        cases impossible

theorem rejectDrain_language :
    (rejectDrain M).generatedLanguage data =
      match result with | .accepted word => {word} | _ => ∅ := by
  cases result with
  | accepted word =>
      ext output
      constructor
      · rintro ⟨bits, _, time, accepted⟩
        have same := (rejectDrain M).halted_outcome_unique data bits time _ _ _ accepted
          (rejectDrain_deterministic_run M deterministic data t (.accepted word) source bits)
        exact Outcome.accepted.inj same
      · intro member
        have equal : output = word := member
        rw [equal]
        exact ⟨[false], by simp, t + 1,
          rejectDrain_deterministic_run M deterministic data t (.accepted word) source [false]⟩
  | rejected =>
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro word ⟨bits, _, accepted⟩
      obtain ⟨word', impossible⟩ := (rejectDrain_accepts_iff M deterministic data t _ source bits).mp ⟨word, accepted⟩
      cases impossible
  | exhausted =>
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro word ⟨bits, _, accepted⟩
      obtain ⟨word', impossible⟩ := (rejectDrain_accepts_iff M deterministic data t _ source bits).mp ⟨word, accepted⟩
      cases impossible

/-- Acceptance of the drained deterministic computation is independent of the
random tape and detects exactly whether its output language is nonempty. -/
theorem rejectDrain_fullTrial (bits : BitString) :
    (rejectDrain M).Accepts data bits ↔ ((rejectDrain M).generatedLanguage data).Nonempty := by
  rw [rejectDrain_accepts_iff M deterministic data t result source bits,
    rejectDrain_language M deterministic data t result source]
  cases result <;> simp

theorem rejectDrain_isGenerator : (rejectDrain M).IsGenerator data := by
  apply Machine.isGenerator_of_full_trials _ _ 0
  · constructor
    · intro bits
      exact ⟨t + bits.length, _, rejectDrain_deterministic_run M deterministic data t result source bits⟩
    · intro bits time rejected
      have same := (rejectDrain M).halted_outcome_unique data bits time _ _ _ rejected
        (rejectDrain_deterministic_run M deterministic data t result source bits)
      cases result <;> cases same
  · intro bits _
    exact rejectDrain_fullTrial M deterministic data t result source bits

theorem rejectDrain_trialBound (seed : ℕ) :
    (rejectDrain M).GeneratorTimeBound data seed (t + seed) := by
  refine ⟨?_, ?_⟩
  · intro bits length
    have halted := rejectDrain_deterministic_run M deterministic data t result source bits
    refine ⟨rejectDrainOutcome result, ?_⟩
    have padded := (rejectDrain M).run_halted_add data bits (t + bits.length) _ halted (seed - bits.length)
    simpa only [Nat.add_assoc, Nat.add_sub_of_le length] using padded
  · intro bits _
    exact rejectDrain_fullTrial M deterministic data t result source bits

omit deterministic source

/-- The concrete recovery machine: replay the certificate and drain randomness
on invalid or incomplete transcripts. Its ordinary input is unused for a
generator source, and its size index is passed directly to that source. -/
def transcriptRecoverer {α : Type} (G : Machine Unit Bool α) : Machine Unit Bool α :=
  rejectDrain (transcriptReplay G)

theorem transcriptRecoverer_isGenerator {α : Type} (G : Machine Unit Bool α)
    (n : ℕ) (certificate : BitString) :
    (transcriptRecoverer G).IsGenerator (generatorData n certificate) := by
  obtain ⟨result, halted⟩ := transcriptReplay_timeBound G (generatorData n certificate) []
  exact rejectDrain_isGenerator (transcriptReplay G) (transcriptReplay_deterministic G)
    _ certificate.length result halted

/-- One random bit suffices for a complete recovery trial. The exact execution
bound is certificate length plus one, for every size and every certificate. -/
theorem transcriptRecoverer_trialBound {α : Type} (G : Machine Unit Bool α)
    (n : ℕ) (certificate : BitString) :
    (transcriptRecoverer G).GeneratorTimeBound (generatorData n certificate) 1 (certificate.length + 1) := by
  obtain ⟨result, halted⟩ := transcriptReplay_timeBound G (generatorData n certificate) []
  exact rejectDrain_trialBound (transcriptReplay G) (transcriptReplay_deterministic G)
    _ certificate.length result halted 1

end

end ComplexityOfGenerators.Simulation
