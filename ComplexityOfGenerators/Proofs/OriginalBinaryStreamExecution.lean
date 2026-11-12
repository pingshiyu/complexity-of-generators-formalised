import ComplexityOfGenerators.Simulation.OriginalBinaryGenerator.Trace
import ComplexityOfGenerators.Proofs.ExpectedOriginalBinarySampling
import ComplexityOfGenerators.Proofs.OriginalSourceWitnesses
import ComplexityOfGenerators.Foundations.FixedBlockPrefix

namespace ComplexityOfGenerators.ExpectedOriginalBinarySampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (families : Bool→UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

/-- Both binary closures execute the same concrete request sampler on the
native machine. Source runtimes receive only a linear charge. -/
theorem native_stream_execution_ae (operation : OriginalBinarySelector.Operation) (n : ℕ)
    (available : Available families operation n) :
    ∀ᵐ stream∂fairCoinMeasure,
      let sample := ((draw families p expected operation n available).run stream).1
      (OriginalBinaryGenerator.machine families p operation).streamProduces (generatorData n) stream
        (SelectedOriginalSampling.outputWord families (width p operation) sample) ∧
      (OriginalBinaryGenerator.machine families p operation).streamRuntime (generatorData n) stream≤
        ((25*(OriginalBinaryGenerator.coefficient families p operation n)^2*(sample.1.1+1)^2+
          (6*n+20)*(SelectedOriginalSampling.sourceRuntime families (width p operation) sample+2) : ℕ) : ℝ≥0∞) := by
  filter_upwards [draw_trace_ae families p expected operation n available] with stream trace
  let sample := ((draw families p expected operation n available).run stream).1
  let requests := SelectedOriginalSampling.selected (width p operation) (selection families p operation) n sample.1
  let records := sample.2
  let offset := SelectedOriginalSampling.outerOffset (width p operation) sample
  let total := offset+SelectedOriginalSampling.sourceCoins (width p operation) sample
  let bits := streamPrefix stream total
  rcases trace with ⟨failed,selected,inner⟩
  have enough : offset≤bits.length := by simp only [bits,streamPrefix_length,total];omega
  have failedPrefix (k : ℕ) (earlier : k<sample.1.1) :
      selection families p operation n ((bits.drop (k*width p operation n)).take (width p operation n))=none := by
    have fits : (k+1)*width p operation n≤total := by
      have scale := Nat.mul_le_mul_right (width p operation n) (show k+1≤sample.1.1+1 by omega)
      exact scale.trans (Nat.le_add_right _ _)
    change selection families p operation n
      (((streamPrefix stream total).drop (k*width p operation n)).take (width p operation n))=none
    rw [streamPrefix_drop_take_fixedBlock_of_le _ _ _ _ fits]
    exact failed k earlier
  have selectedPrefix : selection families p operation n
      ((bits.drop (sample.1.1*width p operation n)).take (width p operation n))=some requests := by
    change selection families p operation n
      (((streamPrefix stream total).drop (sample.1.1*width p operation n)).take (width p operation n))=_
    rw [streamPrefix_drop_take_fixedBlock_of_le _ _ _ _ (by change offset≤total;omega)]
    exact selected
  have sourceTrace : OriginalSourceFamilySampler.FiniteSequenceTrace families bits offset requests records :=
    inner.native_prefix families stream total offset requests records le_rfl
  have count : records.length=requests.length := sourceTrace.length_eq families
  have requestBound : requests.length≤2 :=
    (selection_bounds families p expected operation n _ requests selected).1
  have lengthBound : records.length≤2 := count.trans_le requestBound
  obtain ⟨ticks,bound,run⟩ := OriginalBinaryGenerator.machine_runs_selection_trace families p operation n
    sample.1.1 bits requests records enough failedPrefix selectedPrefix sourceTrace
  have deadline : ticks≤25*(OriginalBinaryGenerator.coefficient families p operation n)^2*(sample.1.1+1)^2+
      (6*n+20)*(SelectedOriginalSampling.sourceRuntime families (width p operation) sample+2) :=
    bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left lengthBound _)) _)
  have cylinder : stream∈cylinder bits := stream_mem_prefix_cylinder stream total
  refine ⟨⟨bits,cylinder,ticks,run⟩,?_⟩
  exact ((OriginalBinaryGenerator.machine families p operation).streamRuntime_le_of_acceptsBy (generatorData n)
    ⟨bits,SelectedOriginalSampling.outputWord families (width p operation) sample,cylinder,run⟩).trans
      (by exact_mod_cast deadline)

end
end ComplexityOfGenerators.ExpectedOriginalBinarySampling
