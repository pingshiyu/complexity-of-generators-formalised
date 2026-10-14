import ComplexityOfGenerators.Simulation.CompositionLanguage
import ComplexityOfGenerators.Proofs.GeneratorCriteria
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

/-!
# Genuine generators from native sequential composition

A bounded sampler and bounded genuine recoverers yield a genuine generator.
On every sufficiently long finite tape, a nonempty sampling language leaves
enough randomness for recovery. Empty sampling languages drain to exhaustion.
These facts establish almost-sure productivity and the Remark 1 trial bounds
without assuming independence of a sampler-selected stopping offset.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)
    (n sampleTime recoveryTime : ℕ)
    (sample : S.TimeBound (generatorData n) sampleTime)
    (recover : ∀ certificate, certificate ∈ S.generatedLanguage (generatorData n) →
      R.IsGenerator (generatorData n certificate) ∧ R.TimeBound (generatorData n certificate) recoveryTime)
    (productive : ∀ bits, (S.generatedLanguage (generatorData n)).Nonempty → sampleTime < bits.length →
      S.Accepts (generatorData n) bits)

include sample recover

def compositionSeed (n sampleTime recoveryTime : ℕ) : ℕ := 2 * n + 4 * sampleTime + recoveryTime + 4

def compositionTime (n sampleTime recoveryTime seed : ℕ) : ℕ :=
  let t := 3 * n + 5 * sampleTime + 5 * recoveryTime + seed + 10
  1 + (t + 1) * (2 * t + 4)

theorem composition_halts_short (seed : ℕ) (bits : BitString) (length : bits.length ≤ seed) :
    (samplerComposition S R).HaltsWithin (generatorData n) bits (compositionTime n sampleTime recoveryTime seed) := by
  obtain ⟨ticks, result, cost, execution, _⟩ := composition_executes S R n sampleTime recoveryTime bits sample
    (fun certificate sampled => (recover certificate sampled).2)
  obtain ⟨nativeTicks, nativeCost, native⟩ := TransducerBank.bank_run (samplerCompositionBank S R) _ bits ticks result execution
  have bound : nativeTicks ≤ compositionTime n sampleTime recoveryTime seed := by
    apply nativeCost.trans
    dsimp [compositionTime]
    have upper : ticks ≤ 3 * n + 5 * sampleTime + 5 * recoveryTime + seed + 10 := by omega
    gcongr
  exact (samplerComposition S R).haltsWithin_mono _ bits bound ⟨result, native⟩

theorem composition_never_rejects (bits : BitString) (t : ℕ) :
    (samplerComposition S R).run (generatorData n) bits t ≠ .halted .rejected := by
  intro rejected
  obtain ⟨ticks, result, _, execution, related⟩ := composition_executes S R n sampleTime recoveryTime bits sample
    (fun certificate sampled => (recover certificate sampled).2)
  obtain ⟨nativeTicks, _, native⟩ := TransducerBank.bank_run (samplerCompositionBank S R) _ bits ticks result execution
  have same := (samplerComposition S R).halted_outcome_unique _ bits t nativeTicks _ _ rejected native
  subst result
  obtain ⟨certificate, sampled, bits, t, rejection⟩ := related
  exact (recover certificate sampled).1.1.2 bits t rejection

include productive

theorem composition_full_trial (bits : BitString) (length : compositionSeed n sampleTime recoveryTime ≤ bits.length) :
    (samplerComposition S R).Accepts (generatorData n) bits ↔
      ((samplerComposition S R).generatedLanguage (generatorData n)).Nonempty := by
  constructor
  · intro accepted
    exact (Machine.generatedLanguage_nonempty_iff_accepts _ _).mpr ⟨bits, accepted⟩
  · intro nonempty
    rw [composition_language S R n sampleTime recoveryTime sample
      (fun certificate sampled => (recover certificate sampled).2)] at nonempty
    obtain ⟨word, certificate, sampled, _⟩ := nonempty
    apply composition_accepts_long S R n sampleTime recoveryTime bits sample
      (productive bits ⟨certificate, sampled⟩ (by simp only [compositionSeed] at length; omega)) recover
    simp only [compositionSeed] at length
    omega

theorem composition_isGenerator : (samplerComposition S R).IsGenerator (generatorData n) := by
  apply Machine.isGenerator_of_full_trials _ _ (compositionSeed n sampleTime recoveryTime)
  · refine ⟨?_, composition_never_rejects S R n sampleTime recoveryTime sample recover⟩
    intro bits
    exact ⟨_, composition_halts_short S R n sampleTime recoveryTime sample recover
      bits.length bits le_rfl⟩
  · intro bits length
    exact composition_full_trial S R n sampleTime recoveryTime sample recover productive
      bits length.symm.le

theorem composition_trialBound : (samplerComposition S R).GeneratorTimeBound (generatorData n)
    (compositionSeed n sampleTime recoveryTime)
    (compositionTime n sampleTime recoveryTime (compositionSeed n sampleTime recoveryTime)) :=
  ⟨composition_halts_short S R n sampleTime recoveryTime sample recover _,
    fun bits length => composition_full_trial S R n sampleTime recoveryTime sample recover productive bits length.symm.le⟩

/-- Increasing the seed allowance also increases the drain budget explicitly. -/
theorem composition_trialBound_of_seed (seed : ℕ) (lower : compositionSeed n sampleTime recoveryTime ≤ seed) :
    (samplerComposition S R).GeneratorTimeBound (generatorData n) seed (compositionTime n sampleTime recoveryTime seed) :=
  ⟨composition_halts_short S R n sampleTime recoveryTime sample recover seed,
    fun bits length => composition_full_trial S R n sampleTime recoveryTime sample recover productive bits (length ▸ lower)⟩

end
end ComplexityOfGenerators
