import ComplexityOfGenerators.Certificates
import ComplexityOfGenerators.Simulation.CertificateVerifier
import ComplexityOfGenerators.Proofs.PolynomialGenerationContainment
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

/-!
# Polynomial verifiers in the native machine model

Every native NP machine yields a deterministic polynomial verifier. Its
certificate is a positive choice tape of length at most the source time bound
plus one. The verifier compiler reads that tape with one native step per source
step. This establishes the verifier-existence part of Theorem 7.1 for `PG`,
without assuming a correspondence with a different computational model.
-/

namespace ComplexityOfGenerators

namespace Machine

variable {I A O : Type} (M : Machine I A O)

/-- An accepting, time-bounded branch has a positive short choice tape. The
extra bit ensures positivity and makes exhaustion impossible on a long prefix. -/
theorem accepts_short_positive_tape (data : InputData I A) (t : ℕ)
    (time : M.TimeBound data t) (bits : BitString) (accepted : M.Accepts data bits) :
    ∃ short : BitString, short ≠ [] ∧ short.length ≤ t + 1 ∧ M.Accepts data short := by
  obtain ⟨word, clock, execution⟩ := accepted
  by_cases length : bits.length ≤ t
  · refine ⟨bits ++ [false], by simp, by simp; omega, word, ?_⟩
    exact M.produces_append data bits [false] word ⟨clock, execution⟩
  · let short := bits.take (t + 1)
    have shortLength : short.length = t + 1 := by simp [short, List.length_take]; omega
    obtain ⟨result, halted⟩ := time short
    have nonexhausted : M.run data short t ≠ .halted .exhausted :=
      M.run_not_exhausted_of_length data short t (by omega)
    have extended := M.run_append_of_not_exhausted data short (bits.drop (t + 1)) t nonexhausted
    have sameTape : short ++ bits.drop (t + 1) = bits := List.take_append_drop _ _
    rw [sameTape, halted] at extended
    have same := M.halted_outcome_unique data bits t clock result (.accepted word) extended execution
    refine ⟨short, ?_, shortLength.le, word, t, ?_⟩
    · intro empty
      simp [empty] at shortLength
    · simpa only [same] using halted

end Machine

/-- Native NP recognition supplies exactly the positive, polynomially bounded
certificates required by Definition 7.2, including for the empty input word. -/
theorem np_has_polynomialVerifier {α : Type} [Fintype α] {L : Language α} (member : L ∈ NP α) :
    Nonempty (PolynomialVerifier L) := by
  obtain ⟨M, p, time, language⟩ := member
  let one : PolynomialBound := ⟨1, 0, by decide⟩
  refine ⟨{
    machine := Simulation.certificateVerifier M
    deterministic := Simulation.certificateVerifier_deterministic M
    time := p
    witnessBound := p.add one
    timeBound := ?_
    complete := ?_
    sound := ?_ }⟩
  · intro w c
    apply Machine.timeBound_mono _ _
      (p.monotone (show w.length ≤ w.length + c.length + 1 by omega))
    exact Simulation.certificateVerifier_timeBound M w c (p w.length) (time w c)
  · intro w member
    obtain ⟨bits, accepted⟩ := (language w).mpr member
    obtain ⟨short, positive, length, produces⟩ := M.accepts_short_positive_tape
      (decisionData w) (p w.length) (time w) bits accepted
    refine ⟨short, positive, ?_, (Simulation.certificateVerifier_accepts M w short []).mpr produces⟩
    exact length.trans (by simpa [one, PolynomialBound.eval] using p.add_le one w.length)
  · intro w c _ accepts
    exact (language w).mp ⟨c, (Simulation.certificateVerifier_accepts M w c []).mp accepts⟩

theorem pg_has_polynomialVerifier {α : Type} [Fintype α] {L : Language α} (member : L ∈ PG α) :
    Nonempty (PolynomialVerifier L) :=
  np_has_polynomialVerifier (pg_subset_np member)

/-- The corrected sampler condition gives an ordinary worst-case time bound
for each recovery call, even on tapes longer than its seed budget. -/
theorem CertificateRecoverer.sampled_timeBound {α : Type} {L : Language α}
    {V : PolynomialVerifier L} (R : CertificateRecoverer V) (S : CertificateGenerator V)
    (n : ℕ) (c : BitString) (sampled : c ∈ S.sampler.layer n) :
    R.machine.TimeBound (generatorData n c) (R.time n c.length) := by
  exact R.machine.generatorTimeBound_timeBound_of_nonempty _ _ _
    (R.timeBound n c (S.certificate_nonempty n c sampled))
    (R.sampled_language_nonempty S n c sampled)

/-- A sampled certificate cannot be longer than the sampler's execution bound,
since a native step emits at most one bit. This holds for every emitted
certificate, not just outputs on full-budget seeds. -/
theorem CertificateGenerator.output_length_le {α : Type} {L : Language α}
    {V : PolynomialVerifier L} (S : CertificateGenerator V) (seed time : PolynomialBound)
    (bound : S.sampler.RunsInTime seed time) (n : ℕ) (c : BitString)
    (sampled : c ∈ S.sampler.layer n) : c.length ≤ time n := by
  have nonempty : (S.sampler.machine.generatedLanguage (generatorData n)).Nonempty := ⟨c, sampled⟩
  have allTapes := S.sampler.machine.generatorTimeBound_timeBound_of_nonempty _ _ _ (bound n) nonempty
  obtain ⟨bits, _, produces⟩ := sampled
  have accepted := S.sampler.machine.produces_at_bound _ bits (time n) c (allTapes bits) produces
  exact S.sampler.machine.accepted_output_length_le _ bits (time n) c accepted

/-- On all sampler outputs, the recovery bound in `(n, |c|)` is bounded by one
polynomial in `n`. Together with `sampled_union_eq`, this discharges the semantic
and resource calculations for the reverse implication of Theorem 7.1; a native
sequential-composition compiler is still needed. -/
theorem CertificateRecoverer.sampled_polynomial_time {α : Type} {L : Language α}
    {V : PolynomialVerifier L} (R : CertificateRecoverer V) (S : CertificateGenerator V) :
    ∃ p : PolynomialBound, ∀ n c, c ∈ S.sampler.layer n →
      R.machine.TimeBound (generatorData n c) (p n) := by
  obtain ⟨seed, time, bound⟩ := S.polynomialTime
  let r : Polynomial ℕ := Polynomial.C R.time.coefficient *
    (Polynomial.X + time.asPolynomial + 1) ^ R.time.degree
  refine ⟨PolynomialBound.ofPolynomial r, fun n c sampled => ?_⟩
  apply Machine.timeBound_mono R.machine _ _ (R.sampled_timeBound S n c sampled)
  have length := S.output_length_le seed time bound n c sampled
  calc
    R.time n c.length ≤ R.time.coefficient * (n + time n + 1) ^ R.time.degree :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ = r.eval n := by
      simp [r, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_add]
    _ ≤ PolynomialBound.ofPolynomial r n := PolynomialBound.eval_le_ofPolynomial r n

end ComplexityOfGenerators
