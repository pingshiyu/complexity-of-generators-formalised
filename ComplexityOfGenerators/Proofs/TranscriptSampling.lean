import ComplexityOfGenerators.Simulation.TranscriptSamplerCorrectness
import ComplexityOfGenerators.Proofs.TranscriptRecovery

/-!
# A polynomial sampler of genuine replay certificates

The finite sampler preserves acceptance on each random tape, hence also the
accepted stream set and almost-sure productivity. Its output always starts
with a padding bit. Every emitted certificate replays to a source output of
the requested length, and every source output has a sampled certificate.
These results include empty words and the empty-generator case.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : Machine I A O)

/-- Acceptance is preserved on a fixed finite tape; totality is required only
of the source computation on that tape. -/
theorem transcriptSampler_accepts_iff (data : InputData I A) (bits : BitString)
    (halts : M.Halts data bits) :
    (transcriptSampler M).Accepts data bits ↔ M.Accepts data bits := by
  obtain ⟨t, result, source⟩ := halts
  obtain ⟨log, _, _, target⟩ := transcriptSampler_run_halted M data bits t result source
  constructor
  · rintro ⟨certificate, time, accepted⟩
    have same := (transcriptSampler M).halted_outcome_unique data bits time _ _ _ accepted target
    cases result with
    | accepted word => exact ⟨word, t, source⟩
    | rejected => cases same
    | exhausted => cases same
  · rintro ⟨word, time, accepted⟩
    have same := M.halted_outcome_unique data bits time _ _ _ accepted source
    subst result
    exact ⟨false :: log, 2 * t + 1, target⟩

theorem transcriptSampler_isGenerator (data : InputData I A) (generator : M.IsGenerator data) :
    (transcriptSampler M).IsGenerator data := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro bits
    obtain ⟨t, result, source⟩ := generator.1.1 bits
    obtain ⟨log, _, _, target⟩ := transcriptSampler_run_halted M data bits t result source
    exact ⟨2 * t + 1, samplerOutcome result (false :: log), target⟩
  · intro bits time rejected
    obtain ⟨t, result, source⟩ := generator.1.1 bits
    obtain ⟨log, _, _, target⟩ := transcriptSampler_run_halted M data bits t result source
    have same := (transcriptSampler M).halted_outcome_unique data bits time _ _ _ rejected target
    cases result with
    | accepted word => cases same
    | exhausted => cases same
    | rejected => exact generator.1.2 bits t source
  · have streams : (transcriptSampler M).acceptedStreams data = M.acceptedStreams data := by
      ext stream
      simp only [Machine.acceptedStreams, Set.mem_ofPred_eq,
        transcriptSampler_accepts_iff M data _ (generator.1.1 _)]
    rw [streams]
    exact generator.2

theorem transcriptSampler_language_nonempty_iff (data : InputData I A)
    (total : ∀ bits, M.Halts data bits) :
    ((transcriptSampler M).generatedLanguage data).Nonempty ↔ (M.generatedLanguage data).Nonempty := by
  constructor
  · rintro ⟨certificate, bits, positive, produced⟩
    obtain ⟨word, accepted⟩ := (transcriptSampler_accepts_iff M data bits (total bits)).mp ⟨certificate, produced⟩
    exact ⟨word, bits, positive, accepted⟩
  · rintro ⟨word, bits, positive, produced⟩
    obtain ⟨certificate, accepted⟩ := (transcriptSampler_accepts_iff M data bits (total bits)).mpr ⟨word, produced⟩
    exact ⟨certificate, bits, positive, accepted⟩

theorem transcriptSampler_trialBound (data : InputData I A) (seed time : ℕ)
    (total : ∀ bits, M.Halts data bits) (bound : M.GeneratorTimeBound data seed time) :
    (transcriptSampler M).GeneratorTimeBound data seed (2 * time + 1) := by
  refine ⟨?_, ?_⟩
  · intro bits length
    obtain ⟨result, source⟩ := bound.1 bits length
    obtain ⟨log, _, _, target⟩ := transcriptSampler_run_halted M data bits time result source
    exact ⟨samplerOutcome result (false :: log), target⟩
  · intro bits length
    rw [transcriptSampler_accepts_iff M data bits (total bits), bound.2 bits length,
      transcriptSampler_language_nonempty_iff M data total]

/-- Every accepted sampler output describes an actual accepted source run on
exactly the same random tape. In particular, padding is never omitted. -/
theorem transcriptSampler_produces_recording (data : InputData I A) (bits certificate : BitString)
    (halts : M.Halts data bits) (sampled : (transcriptSampler M).Produces data bits certificate) :
    ∃ log word, certificate = false :: log ∧
      M.ExecutionTranscript data bits M.initialConfiguration log (.accepted word) := by
  obtain ⟨t, result, source⟩ := halts
  obtain ⟨log, _, recorded, target⟩ := transcriptSampler_run_halted M data bits t result source
  obtain ⟨time, sampled⟩ := sampled
  have same := (transcriptSampler M).halted_outcome_unique data bits time _ _ _ sampled target
  cases result with
  | accepted word => exact ⟨log, word, Outcome.accepted.inj same, recorded⟩
  | rejected => cases same
  | exhausted => cases same

variable {α : Type}

def transcriptUniformSampler (G : UniformGenerators α) : UniformGenerators Bool where
  machine := transcriptSampler G.machine
  isGenerator := fun n => transcriptSampler_isGenerator G.machine (generatorData n) (G.isGenerator n)

theorem transcriptUniformSampler_polynomial (G : UniformGenerators α) (polynomial : G.PolynomialTime) :
    (transcriptUniformSampler G).PolynomialTime := by
  obtain ⟨seed, time, bound⟩ := polynomial
  let two : PolynomialBound := ⟨2, 0, by decide⟩
  let one : PolynomialBound := ⟨1, 0, by decide⟩
  refine ⟨seed, (two.mul time).add one, fun n => ?_⟩
  have trials := transcriptSampler_trialBound G.machine (generatorData n) (seed n) (time n)
    (G.isGenerator n).1.1 (bound n)
  apply Machine.TrialBound.mono_time _ trials
  have upper := PolynomialBound.add_le (two.mul time) one n
  simpa [PolynomialBound.mul, two, one, PolynomialBound.eval, Nat.mul_assoc] using upper

/-- Every sampled certificate recovers an instance of the requested length,
which is the user's added nonempty-recovery condition for Definition 7.4. -/
theorem transcriptSampler_recovers_instance (G : GeneratorFamily α) (n : ℕ) (certificate : BitString)
    (sampled : certificate ∈ (transcriptUniformSampler G.toUniformGenerators).layer n) :
    certificate ≠ [] ∧ ∃ word, word.length = n ∧
      word ∈ (transcriptRecoverer G.machine).generatedLanguage (generatorData n certificate) := by
  obtain ⟨bits, _, produced⟩ := sampled
  obtain ⟨log, word, same, recorded⟩ := transcriptSampler_produces_recording G.machine (generatorData n)
    bits certificate ((G.isGenerator n).1.1 bits) produced
  subst certificate
  refine ⟨by simp, word, ?_, ?_⟩
  · apply G.outputLength n word
    exact ⟨bits ++ [false], by simp,
      G.machine.produces_append (generatorData n) bits [false] word
        ⟨log.length, by simpa only [Machine.runFrom_initial] using recorded.run G.machine⟩⟩
  · rw [transcriptRecoverer_language]
    exact transcriptReplay_accepts_trace G.machine [] n log word (recorded.accepting G.machine) false []

/-- Every source word is recovered from a certificate genuinely emitted by
the sampler, not merely from some hypothetical transcript. -/
theorem transcriptSampler_covers (G : GeneratorFamily α) (n : ℕ) (word : Word α)
    (member : word ∈ G.toUniformGenerators.layer n) :
    ∃ certificate, certificate ∈ (transcriptUniformSampler G.toUniformGenerators).layer n ∧
      word ∈ (transcriptRecoverer G.machine).generatedLanguage (generatorData n certificate) := by
  obtain ⟨bits, positive, t, source⟩ := member
  obtain ⟨log, _, recorded, target⟩ := transcriptSampler_run_halted G.machine (generatorData n) bits t
    (.accepted word) source
  refine ⟨false :: log, ⟨bits, positive, 2 * t + 1, target⟩, ?_⟩
  rw [transcriptRecoverer_language]
  exact transcriptReplay_accepts_trace G.machine [] n log word (recorded.accepting G.machine) false []

/-- The union over sampled certificates is exactly the length slice. -/
theorem transcriptSampler_recovery_union (G : GeneratorFamily α) (n : ℕ) :
    {word | ∃ certificate, certificate ∈ (transcriptUniformSampler G.toUniformGenerators).layer n ∧
      word ∈ (transcriptRecoverer G.machine).generatedLanguage (generatorData n certificate)} =
      G.toUniformGenerators.layer n := by
  ext word
  constructor
  · rintro ⟨certificate, _, recovered⟩
    exact transcriptRecoverer_language_subset G n certificate recovered
  · exact transcriptSampler_covers G n word

end
end ComplexityOfGenerators
