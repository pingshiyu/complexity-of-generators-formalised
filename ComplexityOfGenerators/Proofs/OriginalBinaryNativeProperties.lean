import ComplexityOfGenerators.Proofs.OriginalBinaryStreamExecution
import ComplexityOfGenerators.Proofs.OriginalSourceRuntimeBounds
import ComplexityOfGenerators.Proofs.GeneratedSupportFromStreams

namespace ComplexityOfGenerators.ExpectedOriginalBinarySampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool→UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

include expected in
theorem native_productive (operation : OriginalBinarySelector.Operation) (n : ℕ)
    (available : Available families operation n) :
    fairCoinMeasure ((OriginalBinaryGenerator.machine families p operation).acceptedStreams (generatorData n))=1 := by
  apply (OriginalBinaryGenerator.machine families p operation).acceptedStreams_measure_one_of_ae_streamProduces
    (generatorData n) (fun stream=>SelectedOriginalSampling.outputWord families (width p operation)
      (((draw families p expected operation n available).run stream).1))
  filter_upwards [native_stream_execution_ae families p expected operation n available] with stream execution
  exact execution.1

include expected in
theorem native_expectedLength (mean : ∀ tag,(families tag).ExpectedLength)
    (operation : OriginalBinarySelector.Operation) (n : ℕ) (available : Available families operation n) :
    (OriginalBinaryGenerator.machine families p operation).expectedLength (generatorData n)=(n : ℝ≥0∞) := by
  have paths : ∀ᵐ stream∂fairCoinMeasure,(OriginalBinaryGenerator.machine families p operation).streamProduces
      (generatorData n) stream (SelectedOriginalSampling.outputWord families (width p operation)
        (((draw families p expected operation n available).run stream).1)) := by
    filter_upwards [native_stream_execution_ae families p expected operation n available] with stream execution
    exact execution.1
  rw [(OriginalBinaryGenerator.machine families p operation).expectedLength_eq_of_ae_streamProduces (generatorData n) _ paths]
  exact draw_word_mean families p expected mean operation n available

def outerClock (operation : OriginalBinarySelector.Operation) : PolynomialBound :=
  (⟨25,0,by decide⟩ : PolynomialBound).mul
    ((OriginalBinaryGenerator.coefficient families p operation).mul
      (OriginalBinaryGenerator.coefficient families p operation))

theorem outerClock_eval (operation : OriginalBinarySelector.Operation) (n : ℕ) :
    outerClock families p operation n=25*(OriginalBinaryGenerator.coefficient families p operation n)^2 := by
  rw [outerClock,PolynomialBound.mul_eval,PolynomialBound.mul_eval]
  change 25*(_*_)=25*_^2
  ring

def callClock : PolynomialBound := ⟨26,1,by decide⟩
theorem callClock_lower (n : ℕ) : 6*n+20≤callClock n := by
  change 6*n+20≤26*(n+1)^1
  rw [pow_one]
  omega

def expectedClock (operation : OriginalBinarySelector.Operation) : PolynomialBound :=
  OriginalSourceClosure.expectedClock (outerClock families p operation) callClock p

include expected in
theorem native_expectedRuntime_raw (operation : OriginalBinarySelector.Operation) (n : ℕ)
    (available : Available families operation n) :
    (OriginalBinaryGenerator.machine families p operation).expectedRuntime (generatorData n)≤
      ((25*(OriginalBinaryGenerator.coefficient families p operation n)^2*32+
        (6*n+20)*(2*p n+2) : ℕ) : ℝ≥0∞) := by
  let sampler := draw families p expected operation n available
  have sourceMean := draw_source_runtime_le families p expected operation n available
  have cost := sampler.linear_source_cost (fun sample=>sample.1.1)
    (SelectedOriginalSampling.sourceRuntime families (width p operation))
    (25*(OriginalBinaryGenerator.coefficient families p operation n)^2) (6*n+20) 2 32 (2*p n)
    (draw_outer_secondMoment families p expected operation n available)
    (by simpa only [Nat.cast_mul,Nat.cast_ofNat] using sourceMean)
  apply le_trans _ cost
  apply lintegral_mono_ae
  filter_upwards [native_stream_execution_ae families p expected operation n available] with stream execution
  exact execution.2

include expected in
theorem native_expectedRuntime (operation : OriginalBinarySelector.Operation) (n : ℕ)
    (available : Available families operation n) :
    (OriginalBinaryGenerator.machine families p operation).expectedRuntime (generatorData n)≤
      (expectedClock families p operation n : ℝ≥0∞) := by
  apply (native_expectedRuntime_raw families p expected operation n available).trans
  apply Nat.cast_le.mpr
  rw [←outerClock_eval]
  have sourceBound : 2*p n+2≤(n+2)*p n+n+3 := by nlinarith
  have outerBound : outerClock families p operation n*32≤32*outerClock families p operation n := by omega
  exact (Nat.add_le_add outerBound (Nat.mul_le_mul (callClock_lower n) sourceBound)).trans
    (OriginalSourceClosure.expectedClock_lower (outerClock families p operation) callClock p n)

end
end ComplexityOfGenerators.ExpectedOriginalBinarySampling
