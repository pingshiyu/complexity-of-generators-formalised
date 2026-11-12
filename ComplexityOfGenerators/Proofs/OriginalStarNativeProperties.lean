import ComplexityOfGenerators.Proofs.OriginalStarStreamExecution
import ComplexityOfGenerators.Proofs.OriginalSourceRuntimeBounds
import ComplexityOfGenerators.Proofs.GeneratedSupportFromStreams

namespace ComplexityOfGenerators.ExpectedOriginalStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

include expected in
theorem native_productive (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    fairCoinMeasure ((OriginalStarGenerator.machine G.machine p).acceptedStreams (generatorData n))=1 := by
  apply (OriginalStarGenerator.machine G.machine p).acceptedStreams_measure_one_of_ae_streamProduces (generatorData n)
    (fun stream=>outputWord G (((draw G p expected n available).run stream).1))
  filter_upwards [native_stream_execution_ae G p expected n available] with stream execution
  exact execution.1

include expected in
theorem native_expectedLength (mean : G.ExpectedLength) (n : ℕ)
    (available : ExpectedStarSampling.Available G n) :
    (OriginalStarGenerator.machine G.machine p).expectedLength (generatorData n)=(n : ℝ≥0∞) := by
  have paths : ∀ᵐ stream∂fairCoinMeasure,(OriginalStarGenerator.machine G.machine p).streamProduces
      (generatorData n) stream (outputWord G (((draw G p expected n available).run stream).1)) := by
    filter_upwards [native_stream_execution_ae G p expected n available] with stream execution
    exact execution.1
  rw [(OriginalStarGenerator.machine G.machine p).expectedLength_eq_of_ae_streamProduces (generatorData n) _ paths]
  exact draw_word_mean G p expected mean n available

def outerClock : PolynomialBound :=
  (⟨25,0,by decide⟩ : PolynomialBound).mul
    ((ExpectedOriginalStarController.primitiveCoefficient G.machine p).mul
      (ExpectedOriginalStarController.primitiveCoefficient G.machine p))

theorem outerClock_eval (n : ℕ) : outerClock G p n=25*(ExpectedOriginalStarController.primitiveCoefficient G.machine p n)^2 := by
  rw [outerClock,PolynomialBound.mul_eval,PolynomialBound.mul_eval]
  change 25*(_*_)=25*_^2
  ring

def callClock : PolynomialBound := ⟨26,1,by decide⟩
theorem callClock_lower (n : ℕ) : 6*n+20≤callClock n := by
  change 6*n+20≤26*(n+1)^1
  rw [pow_one]
  omega

def expectedClock : PolynomialBound := OriginalSourceClosure.expectedClock (outerClock G p) callClock p

include expected in
theorem native_expectedRuntime_raw (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    (OriginalStarGenerator.machine G.machine p).expectedRuntime (generatorData n)≤
      ((25*(ExpectedOriginalStarController.primitiveCoefficient G.machine p n)^2*8+
        (6*n+20)*(n*p n+n) : ℕ) : ℝ≥0∞) := by
  let sampler := draw G p expected n available
  have sourceMean := draw_source_runtime_le G p expected n available
  have cost := sampler.linear_source_cost (fun result=>result.1.1) (sourceRuntime G)
    (25*(ExpectedOriginalStarController.primitiveCoefficient G.machine p n)^2) (6*n+20) n 8 (n*p n)
    (draw_outer_secondMoment G p expected n available) (by simpa only [Nat.cast_mul] using sourceMean)
  apply le_trans _ cost
  apply lintegral_mono_ae
  filter_upwards [native_stream_execution_ae G p expected n available] with stream execution
  exact execution.2

include expected in
theorem native_expectedRuntime (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    (OriginalStarGenerator.machine G.machine p).expectedRuntime (generatorData n)≤(expectedClock G p n : ℝ≥0∞) := by
  apply (native_expectedRuntime_raw G p expected n available).trans
  apply Nat.cast_le.mpr
  rw [←outerClock_eval]
  have sourceBound : n*p n+n≤(n+2)*p n+n+3 := by nlinarith
  have outerBound : outerClock G p n*8≤32*outerClock G p n := by omega
  exact (Nat.add_le_add outerBound (Nat.mul_le_mul (callClock_lower n) sourceBound)).trans
    (OriginalSourceClosure.expectedClock_lower (outerClock G p) callClock p n)

end
end ComplexityOfGenerators.ExpectedOriginalStarSampling
