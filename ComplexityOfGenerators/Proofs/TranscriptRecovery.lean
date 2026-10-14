import ComplexityOfGenerators.Proofs.ReplayGenerators
import ComplexityOfGenerators.Simulation.TranscriptReplaySoundness
import ComplexityOfGenerators.Certificates
import ComplexityOfGenerators.Foundations.TrialBounds
import ComplexityOfGenerators.Foundations.ResourceBounds

/-!
# Transcript recovery: support, completeness and polynomial bounds

This is a concrete native recovery machine for the forward direction of 7.1.
Its language is exactly the singleton replay output, or empty for an invalid
certificate. Every recovered word belongs to the source slice, and every source
word has a positive certificate. For polynomial-time generators, these
certificates have polynomial length. `TranscriptSampling` constructs the
matching sampler; `TranscriptScheme` assembles both components conditional on
a correct replay verifier, whose native construction remains unfinished.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type}

theorem transcriptRecoverer_language (M : Machine Unit Bool α) (n : ℕ) (c : BitString) :
    (transcriptRecoverer M).generatedLanguage (generatorData n c) =
      {w | (transcriptReplay M).run (generatorData n c) [] c.length = .halted (.accepted w)} := by
  obtain ⟨result, halted⟩ := transcriptReplay_timeBound M (generatorData n c) []
  change (transcriptReplay M).run (generatorData n c) [] c.length = .halted result at halted
  have language := rejectDrain_language (transcriptReplay M) (transcriptReplay_deterministic M)
    (generatorData n c) c.length result halted
  change (rejectDrain (transcriptReplay M)).generatedLanguage _ = _
  rw [language]
  ext word
  simp only [Set.mem_ofPred_eq, halted]
  cases result <;> simp [eq_comm]

/-- Soundness for all certificates, not just those a sampler happens to emit. -/
theorem transcriptRecoverer_language_subset (G : GeneratorFamily α) (n : ℕ) (c : BitString) :
    (transcriptRecoverer G.machine).generatedLanguage (generatorData n c) ⊆
      G.toUniformGenerators.layer n := by
  intro word member
  rw [transcriptRecoverer_language] at member
  obtain ⟨bits, accepted⟩ := transcriptReplay_sound G.machine [] n c [] word member
  exact ⟨bits ++ [false], by simp,
    G.machine.produces_append (generatorData n) bits [false] word accepted⟩

theorem transcriptRecoverer_outputs_length (G : GeneratorFamily α) (n : ℕ) (c : BitString)
    (word : Word α) (member : word ∈ (transcriptRecoverer G.machine).generatedLanguage (generatorData n c)) :
    word.length = n :=
  G.outputLength n word (transcriptRecoverer_language_subset G n c member)

/-- Every genuine source output has a positive replay certificate. -/
theorem transcriptRecoverer_complete (G : GeneratorFamily α) (n : ℕ) (word : Word α)
    (member : word ∈ G.toUniformGenerators.layer n) :
    ∃ c : BitString, c ≠ [] ∧ word ∈ (transcriptRecoverer G.machine).generatedLanguage (generatorData n c) := by
  obtain ⟨bits, _, t, accepted⟩ := member
  obtain ⟨c, positive, _, replay⟩ := transcriptReplay_complete G.machine [] n bits t word accepted
  refine ⟨c, positive, ?_⟩
  rw [transcriptRecoverer_language]
  exact replay

/-- All positive certificates together recover precisely the source slice. -/
theorem transcriptRecoverer_union (G : GeneratorFamily α) (n : ℕ) :
    {w | ∃ c : BitString, c ≠ [] ∧
      w ∈ (transcriptRecoverer G.machine).generatedLanguage (generatorData n c)} =
      G.toUniformGenerators.layer n := by
  ext word
  constructor
  · rintro ⟨c, _, recovered⟩
    exact transcriptRecoverer_language_subset G n c recovered
  · exact transcriptRecoverer_complete G n word

/-- The existing Remark 1 budgets give a polynomial-size certificate for
every source word; no lower bound on its sampling probability is needed. -/
theorem transcriptRecoverer_bounded_complete (G : GeneratorFamily α) (seed time : PolynomialBound)
    (bound : G.toUniformGenerators.RunsInTime seed time) (n : ℕ) (word : Word α)
    (member : word ∈ G.toUniformGenerators.layer n) :
    ∃ c : BitString, c ≠ [] ∧ c.length ≤ time n + 1 ∧
      word ∈ (transcriptRecoverer G.machine).generatedLanguage (generatorData n c) := by
  obtain ⟨bits, _, accepted⟩ := (G.machine.generatedLanguage_iff_budget_seed
    (generatorData n) (seed n) (time n) (seed.positive n) (bound n) word).mp member
  obtain ⟨c, positive, length, replay⟩ := transcriptReplay_complete G.machine [] n bits (time n) word accepted
  refine ⟨c, positive, length, ?_⟩
  rw [transcriptRecoverer_language]
  exact replay

/-- The recovery seed bound is one and its bivariate time bound is `n+|c|+1`.
This includes invalid certificates, empty slices, and the size-zero slice. -/
theorem transcriptRecoverer_polynomial_trials (M : Machine Unit Bool α) :
    ∃ seed time : BivariatePolynomialBound, ∀ n c,
      (transcriptRecoverer M).GeneratorTimeBound (generatorData n c)
        (seed n c.length) (time n c.length) := by
  refine ⟨⟨1, 0, by decide⟩, ⟨1, 1, by decide⟩, fun n c => ?_⟩
  apply Machine.TrialBound.mono_time _ (transcriptRecoverer_trialBound M n c)
  simp [BivariatePolynomialBound.eval]

end
end ComplexityOfGenerators
