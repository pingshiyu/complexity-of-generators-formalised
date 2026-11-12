import ComplexityOfGenerators.Proofs.ExpectedStarStreamExecution
import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Support

namespace ComplexityOfGenerators.ExpectedStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ExpectedStarGenerator.machine
variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))
    (P : BoundedPhaseFamily α) (layers : ∀ n, P.layer n = G.layer n)

include expected layers in
theorem native_productive (n : ℕ) (available : Available G n) :
    fairCoinMeasure ((ExpectedStarGenerator.machine G.machine p P).acceptedStreams (generatorData n)) = 1 := by
  have accepted : ∀ᵐ stream ∂fairCoinMeasure,
      stream ∈ (ExpectedStarGenerator.machine G.machine p P).acceptedStreams (generatorData n) := by
    filter_upwards [native_stream_execution_ae G p expected P layers n available] with stream execution
    obtain ⟨bits,member,produced⟩ := execution.1
    exact ⟨bits,member,outputWord (((draw G p expected P layers n available).run stream).1),produced⟩
  have null : fairCoinMeasure ((ExpectedStarGenerator.machine G.machine p P).acceptedStreams (generatorData n))ᶜ = 0 :=
    ae_iff.mp accepted
  have sum := measure_add_measure_compl (μ := fairCoinMeasure)
    ((ExpectedStarGenerator.machine G.machine p P).measurableSet_acceptedStreams (generatorData n))
  rw [null,add_zero,measure_univ] at sum
  exact sum

include expected layers in
theorem native_expectedLength (n : ℕ) (available : Available G n) :
    (ExpectedStarGenerator.machine G.machine p P).expectedLength (generatorData n) = (n : ℝ≥0∞) := by
  change (∫⁻ stream, ((ExpectedStarGenerator.machine G.machine p P).streamLength (generatorData n) stream : ℝ≥0∞)
    ∂fairCoinMeasure) = _
  calc
    _ = ∫⁻ stream, ((outputWord (((draw G p expected P layers n available).run stream).1)).length : ℝ≥0∞)
        ∂fairCoinMeasure := by
      apply lintegral_congr_ae
      filter_upwards [native_stream_execution_ae G p expected P layers n available] with stream execution
      exact congrArg (fun length : ℕ => (length : ℝ≥0∞))
        ((ExpectedStarGenerator.machine G.machine p P).streamLength_of_produces (generatorData n) execution.1)
    _ = _ := draw_word_mean G p expected P layers n available

include expected layers in
theorem native_expectedRuntime_raw (n : ℕ) (available : Available G n) :
    (ExpectedStarGenerator.machine G.machine p P).expectedRuntime (generatorData n) ≤
      ((25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P n)^2*
        (36+6*n^2*(P.reciprocal n)^2) : ℕ) : ℝ≥0∞) := by
  let constant : ℕ := 25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P n)^2
  let cost : BitStream → ℝ≥0∞ := fun stream =>
    (((totalAttempts (((draw G p expected P layers n available).run stream).1)+1 : ℕ) : ℝ≥0∞)^2)
  have measurable : Measurable cost := (measurable_of_countable (fun result : DrawResult p n α =>
    (((totalAttempts result+1 : ℕ) : ℝ≥0∞)^2))).comp
      (measurable_fst.comp (draw G p expected P layers n available).measurable)
  change (∫⁻ stream, (ExpectedStarGenerator.machine G.machine p P).streamRuntime (generatorData n) stream
    ∂fairCoinMeasure) ≤ _
  calc
    _ ≤ ∫⁻ stream, (constant : ℝ≥0∞)*cost stream ∂fairCoinMeasure := by
      apply lintegral_mono_ae
      filter_upwards [native_stream_execution_ae G p expected P layers n available] with stream execution
      simpa only [constant,cost,Nat.cast_mul,Nat.cast_pow] using execution.2
    _ = (constant : ℝ≥0∞)*(∫⁻ stream, cost stream ∂fairCoinMeasure) := lintegral_const_mul _ measurable
    _ ≤ (constant : ℝ≥0∞)*(36+6*(n : ℝ≥0∞)^2*(P.reciprocal n : ℝ≥0∞)^2) :=
      mul_le_mul' le_rfl (draw_charged_secondMoment G p expected P layers n available)
    _ = _ := by simp only [constant,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_ofNat]

noncomputable def expectedClock : PolynomialBound := PolynomialBound.ofPolynomial
  (25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P).asPolynomial^2*
    (36+6*Polynomial.X^2*P.reciprocal.asPolynomial^2))

theorem expectedClock_lower (n : ℕ) :
    25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P n)^2*(36+6*n^2*(P.reciprocal n)^2) ≤
      expectedClock G p P n := by
  have lower := PolynomialBound.eval_le_ofPolynomial
    (25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P).asPolynomial^2*
      (36+6*Polynomial.X^2*P.reciprocal.asPolynomial^2)) n
  simpa only [expectedClock,Polynomial.eval_mul,Polynomial.eval_add,Polynomial.eval_pow,
    Polynomial.eval_X,Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval] using lower

include expected layers in
theorem native_expectedRuntime (n : ℕ) (available : Available G n) :
    (ExpectedStarGenerator.machine G.machine p P).expectedRuntime (generatorData n) ≤ (expectedClock G p P n : ℝ≥0∞) :=
  (native_expectedRuntime_raw G p expected P layers n available).trans (Nat.cast_le.mpr (expectedClock_lower G p P n))

end
end ComplexityOfGenerators.ExpectedStarSampling
