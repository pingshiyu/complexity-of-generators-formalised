import ComplexityOfGenerators.PaperCertificates
import ComplexityOfGenerators.Proofs.PaperCertificateBounds
import ComplexityOfGenerators.Proofs.PaperCertificateComposition
import ComplexityOfGenerators.Proofs.CertificateSchemeGeneration

/-! Compose the current paper's certificate sampler and recoverer. No positive
certificate restriction or finite-trial runtime premise is used. -/
namespace ComplexityOfGenerators.PaperCertificates
open Simulation
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] {L : Language α} {V : PolynomialVerifier L}

theorem CertificateRecoverer.sampled_nonempty (R : CertificateRecoverer V)
    (S : CertificateGenerator V) (n : ℕ) (certificate : Word α)
    (sampled : certificate∈S.sampler.layer n) :
    (R.machine.generatedLanguage (recoveryInput n certificate)).Nonempty := by
  rw [R.recovers]
  exact S.certifiesInstance n certificate sampled

theorem CertificateRecoverer.sampled_timeBound (R : CertificateRecoverer V)
    (S : CertificateGenerator V) (n : ℕ) (certificate : Word α)
    (sampled : certificate∈S.sampler.layer n) :
    R.machine.TimeBound (recoveryInput n certificate) (R.time n certificate.length) :=
  R.machine.accepting_timeBound_of_nonempty _ _ (R.isGenerator n certificate)
    (R.accepting_time n certificate) (R.sampled_nonempty S n certificate sampled)

theorem CertificateGenerator.output_length_le (S : CertificateGenerator V) (n : ℕ)
    (certificate : Word α) (sampled : certificate∈S.sampler.layer n) : certificate.length≤S.time n := by
  obtain ⟨bits,_,produced⟩ := sampled
  exact S.sampler.machine.accepted_output_length_le _ bits (S.time n) certificate
    (S.accepting_time n bits certificate produced)

theorem CertificateRecoverer.sampled_polynomial_time (R : CertificateRecoverer V)
    (S : CertificateGenerator V) : ∃ p : PolynomialBound,∀ n certificate,certificate∈S.sampler.layer n→
      R.machine.TimeBound (recoveryInput n certificate) (p n) := by
  let polynomial : Polynomial ℕ := Polynomial.C R.time.coefficient *
    (Polynomial.X+S.time.asPolynomial+1)^R.time.degree
  refine ⟨PolynomialBound.ofPolynomial polynomial,?_⟩
  intro n certificate sampled
  apply Machine.timeBound_mono R.machine _ _ (R.sampled_timeBound S n certificate sampled)
  have length := S.output_length_le n certificate sampled
  calc
    R.time n certificate.length≤R.time.coefficient*(n+S.time n+1)^R.time.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _=polynomial.eval n := by simp [polynomial,Polynomial.eval_mul,Polynomial.eval_pow,Polynomial.eval_add]
    _≤PolynomialBound.ofPolynomial polynomial n := PolynomialBound.eval_le_ofPolynomial polynomial n

theorem CertificateRecoverer.sampled_union_eq (R : CertificateRecoverer V)
    (S : CertificateGenerator V) (n : ℕ) :
    {word | ∃ certificate,certificate∈S.sampler.layer n ∧
      word∈R.machine.generatedLanguage (recoveryInput n certificate)}=lengthSlice L n := by
  ext word
  constructor
  · rintro ⟨certificate,_,member⟩
    rw [R.recovers] at member
    exact member.1
  · intro member
    have covered := member
    rw [S.covers] at covered
    obtain ⟨_,certificate,sampled,certified⟩ := covered
    exact ⟨certificate,sampled,by rw [R.recovers];exact ⟨member,certified⟩⟩

theorem certificateScheme_mem_pg (S : CertificateGenerator V) (R : CertificateRecoverer V) : L∈PG α := by
  obtain ⟨recoveryTime,recoveryBound⟩ := R.sampled_polynomial_time S
  let sampleTime := schemeClockBudget S.time
  let clockedSampler := familyClock S.sampler.machine S.time
  let composed := samplerComposition clockedSampler R.machine
  have clockBound (n : ℕ) : clockedSampler.TimeBound (generatorData n) (sampleTime n) := by
    apply Machine.timeBound_mono _ _ _ (familyClock_timeBound S.sampler.machine S.time n)
    have bound := (polynomialClockTime S.time).add_le S.time n
    change polynomialClockTime S.time n≤(polynomialClockTime S.time).add S.time n
    omega
  have language (n : ℕ) : clockedSampler.generatedLanguage (generatorData n)=S.sampler.layer n := by
    ext word
    change (∃ bits,bits≠[] ∧ clockedSampler.Produces (generatorData n) bits word)↔_
    simp only [clockedSampler,AcceptingTimeGeneration.clock_produces_iff S.sampler S.time S.accepting_time]
    rfl
  have recover (n : ℕ) (certificate : Word α)
      (sampled : certificate∈clockedSampler.generatedLanguage (generatorData n)) :
      R.machine.IsGenerator (certificateData n certificate) ∧
      R.machine.TimeBound (certificateData n certificate) (recoveryTime n) := by
    rw [language] at sampled
    exact ⟨R.isGenerator n certificate,recoveryBound n certificate sampled⟩
  have productive (n : ℕ) (bits : BitString)
      (nonempty : (clockedSampler.generatedLanguage (generatorData n)).Nonempty)
      (long : sampleTime n<bits.length) : clockedSampler.Accepts (generatorData n) bits := by
    rw [language] at nonempty
    have smaller : S.time n≤sampleTime n := by
      have bound := (polynomialClockTime S.time).add_le S.time n
      change S.time n≤(polynomialClockTime S.time).add S.time n
      omega
    obtain ⟨certificate,accepted⟩ := S.sampler.machine.accepts_long_tape_of_acceptingTimeBound _ _
      (S.sampler.isGenerator n) (S.accepting_time n) bits (by omega) nonempty
    exact ⟨certificate,(AcceptingTimeGeneration.clock_produces_iff S.sampler S.time S.accepting_time n bits certificate).mpr accepted⟩
  have generates (n : ℕ) : composed.generatedLanguage (generatorData n)=lengthSlice L n := by
    rw [composition_language clockedSampler R.machine n (sampleTime n) (recoveryTime n) (clockBound n)
      (fun certificate sampled=>(recover n certificate sampled).2)]
    simp only [language]
    exact R.sampled_union_eq S n
  refine mem_pg_of_lengthSlices L composed (schemeSeed sampleTime recoveryTime)
    (schemeTime sampleTime recoveryTime) ?_ generates ?_
  · intro n
    exact PaperCertificateComposition.composition_isGenerator clockedSampler R.machine n
      (sampleTime n) (recoveryTime n) (clockBound n) (recover n) (productive n)
  · intro n
    apply Machine.TrialBound.mono_time _
      (PaperCertificateComposition.composition_trialBound_of_seed clockedSampler R.machine n
        (sampleTime n) (recoveryTime n) (clockBound n) (recover n) (productive n)
          (schemeSeed sampleTime recoveryTime n) (schemeSeed_bound _ _ n))
    exact schemeTime_bound _ _ n

theorem hasCertificateScheme_mem_pg (scheme : HasCertificateScheme V) : L∈PG α := by
  obtain ⟨⟨S⟩,⟨R⟩⟩ := scheme
  exact certificateScheme_mem_pg S R

end
end ComplexityOfGenerators.PaperCertificates
