import ComplexityOfGenerators.Proofs.GeneratorComposition
import ComplexityOfGenerators.Proofs.PolynomialVerifiers
import ComplexityOfGenerators.Simulation.FamilyClock
import ComplexityOfGenerators.Foundations.TrialBounds

/-!
# The reverse implication of Theorem 7.1

The sampler is clocked using its polynomial index bound, then compiled with
the recoverer through the verified finite-bank program. The added condition
that every sampled certificate certifies an instance ensures every actual
recovery call has an ordinary polynomial time bound.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] {L : Language α} {V : PolynomialVerifier L}
    (S : CertificateGenerator V) (R : CertificateRecoverer V)

/-- One budget dominates both the clock compiler and the original sampler. -/
def schemeClockBudget (time : PolynomialBound) : PolynomialBound :=
  (polynomialClockTime time).add time

def schemeSeedPolynomial (sample recovery : PolynomialBound) : Polynomial ℕ :=
  2 * Polynomial.X + 4 * sample.asPolynomial + recovery.asPolynomial + 4

def schemeSeed (sample recovery : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (schemeSeedPolynomial sample recovery)

def schemeTimePolynomial (sample recovery : PolynomialBound) : Polynomial ℕ :=
  let ticks := 3 * Polynomial.X + 5 * sample.asPolynomial + 5 * recovery.asPolynomial +
    (schemeSeed sample recovery).asPolynomial + 10
  1 + (ticks + 1) * (2 * ticks + 4)

def schemeTime (sample recovery : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (schemeTimePolynomial sample recovery)

theorem schemeSeed_bound (sample recovery : PolynomialBound) (n : ℕ) :
    compositionSeed n (sample n) (recovery n) ≤ schemeSeed sample recovery n := by
  simpa [schemeSeedPolynomial, compositionSeed, schemeSeed, Polynomial.eval_add,
    Polynomial.eval_mul] using
    PolynomialBound.eval_le_ofPolynomial (schemeSeedPolynomial sample recovery) n

theorem schemeTime_bound (sample recovery : PolynomialBound) (n : ℕ) :
    compositionTime n (sample n) (recovery n) (schemeSeed sample recovery n) ≤
      schemeTime sample recovery n := by
  simpa [schemeTimePolynomial, compositionTime, schemeTime, Polynomial.eval_add,
    Polynomial.eval_mul] using
    PolynomialBound.eval_le_ofPolynomial (schemeTimePolynomial sample recovery) n

include S R in
/-- A full native polynomial generator from the two certificate-scheme components. -/
theorem certificateScheme_mem_pg : L ∈ PG α := by
  obtain ⟨seed, time, samplerBound⟩ := S.polynomialTime
  obtain ⟨recoveryTime, recoveryBound⟩ := R.sampled_polynomial_time S
  let sampleTime := schemeClockBudget time
  let clockedSampler := familyClock S.sampler.machine time
  let composed := samplerComposition clockedSampler R.machine
  have clockBound (n : ℕ) : clockedSampler.TimeBound (generatorData n) (sampleTime n) := by
    apply Machine.timeBound_mono _ _ _ (familyClock_timeBound S.sampler.machine time n)
    have bound := (polynomialClockTime time).add_le time n
    change polynomialClockTime time n ≤ (polynomialClockTime time).add time n
    omega
  have language (n : ℕ) :
      clockedSampler.generatedLanguage (generatorData n) = S.sampler.layer n := by
    exact familyClock_generatedLanguage S.sampler.machine time n (seed n) (samplerBound n)
  -- Productivity of sampled certificates supplies both recovery hypotheses.
  have recover (n : ℕ) (certificate : BitString)
      (sampled : certificate ∈ clockedSampler.generatedLanguage (generatorData n)) :
      R.machine.IsGenerator (generatorData n certificate) ∧
        R.machine.TimeBound (generatorData n certificate) (recoveryTime n) := by
    rw [language n] at sampled
    exact ⟨R.isGenerator n certificate (S.certificate_nonempty n certificate sampled),
      recoveryBound n certificate sampled⟩
  have productive (n : ℕ) (bits : BitString)
      (nonempty : (clockedSampler.generatedLanguage (generatorData n)).Nonempty)
      (long : sampleTime n < bits.length) : clockedSampler.Accepts (generatorData n) bits := by
    rw [language n] at nonempty
    have ordinary := S.sampler.machine.generatorTimeBound_timeBound_of_nonempty _
      (seed n) (time n) (samplerBound n) nonempty
    have smaller : time n ≤ sampleTime n := by
      have bound := (polynomialClockTime time).add_le time n
      change time n ≤ (polynomialClockTime time).add time n
      omega
    obtain ⟨certificate, accepted⟩ :=
      S.sampler.machine.accepts_at_timeBound_of_long_tape _ (time n)
        (S.sampler.isGenerator n) ordinary bits (by omega)
    exact ⟨certificate, (familyClock_preserves S.sampler.machine time n (seed n)
      (samplerBound n) bits certificate).mpr ⟨time n, accepted⟩⟩
  have generates (n : ℕ) : composed.generatedLanguage (generatorData n) = lengthSlice L n := by
    rw [composition_language clockedSampler R.machine n (sampleTime n) (recoveryTime n) (clockBound n)
      (fun certificate sampled => (recover n certificate sampled).2)]
    simp only [language n]
    exact R.sampled_union_eq S n
  -- The composition lemmas discharge the machine obligations; the shared
  -- criterion supplies exact output lengths and the union over all sizes.
  refine mem_pg_of_lengthSlices L composed (schemeSeed sampleTime recoveryTime)
    (schemeTime sampleTime recoveryTime) ?_ generates ?_
  · intro n
    exact composition_isGenerator clockedSampler R.machine n (sampleTime n) (recoveryTime n)
      (clockBound n) (recover n) (productive n)
  · intro n
    apply Machine.TrialBound.mono_time _
      (composition_trialBound_of_seed clockedSampler R.machine n (sampleTime n)
        (recoveryTime n) (clockBound n) (recover n) (productive n)
        (schemeSeed sampleTime recoveryTime n) (schemeSeed_bound _ _ n))
    exact schemeTime_bound _ _ n

theorem hasCertificateScheme_mem_pg (scheme : HasCertificateScheme V) : L ∈ PG α := by
  obtain ⟨⟨S⟩, ⟨R⟩⟩ := scheme
  exact certificateScheme_mem_pg S R

end
end ComplexityOfGenerators
