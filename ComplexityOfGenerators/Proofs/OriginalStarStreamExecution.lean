import ComplexityOfGenerators.Simulation.OriginalStarGenerator.Trace
import ComplexityOfGenerators.Proofs.ExpectedOriginalStarSampling
import ComplexityOfGenerators.Proofs.OriginalSourceWitnesses
import ComplexityOfGenerators.Foundations.FixedBlockPrefix

namespace ComplexityOfGenerators.ExpectedOriginalStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

/-- The original-source sampler describes one genuine fair-stream execution
of the native star generator, with only a linear charge for source runtimes. -/
theorem native_stream_execution_ae (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    ∀ᵐ stream∂fairCoinMeasure,
      let sample := ((draw G p expected n available).run stream).1
      (OriginalStarGenerator.machine G.machine p).streamProduces (generatorData n) stream (outputWord G sample) ∧
      (OriginalStarGenerator.machine G.machine p).streamRuntime (generatorData n) stream≤
        ((25*(ExpectedOriginalStarController.primitiveCoefficient G.machine p n)^2*(sample.1.1+1)^2+
          (6*n+20)*(sourceRuntime G sample+n) : ℕ) : ℝ≥0∞) := by
  filter_upwards [draw_trace_ae G p expected n available] with stream trace
  let sample := ((draw G p expected n available).run stream).1
  let parts := ExpectedStarSampling.chosenParts G p n (List.ofFn sample.1.2)
  let records := sample.2
  let offset := outerOffset sample
  let total := offset+sourceCoins sample
  let bits := streamPrefix stream total
  rcases trace with ⟨failed,accepted,productive,inner⟩
  have enough : offset≤bits.length := by simp only [bits,streamPrefix_length,total]; omega
  have failedPrefix (k : ℕ) (earlier : k<sample.1.1) :
      CertifiedStarPhase.value G.machine p n
        ((bits.drop (k*StarCertification.width p n)).take (StarCertification.width p n))=none := by
    have fits : (k+1)*StarCertification.width p n≤total := by
      have scale := Nat.mul_le_mul_right (StarCertification.width p n) (show k+1≤sample.1.1+1 by omega)
      exact scale.trans (Nat.le_add_right _ _)
    change CertifiedStarPhase.value G.machine p n
      (((streamPrefix stream total).drop (k*StarCertification.width p n)).take (StarCertification.width p n))=none
    rw [streamPrefix_drop_take_fixedBlock_of_le _ _ _ _ fits]
    exact failed k earlier
  have acceptedPrefix : CertifiedStarPhase.value G.machine p n
      ((bits.drop (sample.1.1*StarCertification.width p n)).take (StarCertification.width p n))=
        some (StarPaths.payload parts) := by
    change CertifiedStarPhase.value G.machine p n
      (((streamPrefix stream total).drop (sample.1.1*StarCertification.width p n)).take (StarCertification.width p n))=_
    rw [streamPrefix_drop_take_fixedBlock_of_le _ _ _ _ (by change offset≤total; omega)]
    exact accepted
  have sourceTrace : OriginalSourceFamilySampler.FiniteSequenceTrace (families G) bits offset
      (parts.map (fun j=>(false,j))) records :=
    inner.native_prefix (families G) stream total offset _ _ le_rfl
  have count : records.length=parts.length := by
    simpa only [List.length_map] using sourceTrace.length_eq (families G)
  have lengthBound : records.length≤n := by
    rw [count]
    exact (ExpectedStarGenerator.positive_length_le_sum parts (fun j member=>(productive.2 j member).1)).trans_eq productive.1
  obtain ⟨ticks,bound,run⟩ := OriginalStarGenerator.machine_runs_trace G p n sample.1.1 parts records bits
    productive.1 (fun j member=>(productive.2 j member).1) enough failedPrefix acceptedPrefix sourceTrace
  have deadline : ticks≤25*(ExpectedOriginalStarController.primitiveCoefficient G.machine p n)^2*(sample.1.1+1)^2+
      (6*n+20)*(sourceRuntime G sample+n) := by
    exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_left lengthBound _)) _)
  have cylinder : stream∈cylinder bits := stream_mem_prefix_cylinder stream total
  refine ⟨⟨bits,cylinder,ticks,run⟩,?_⟩
  exact ((OriginalStarGenerator.machine G.machine p).streamRuntime_le_of_acceptsBy (generatorData n)
    ⟨bits,outputWord G sample,cylinder,run⟩).trans (by exact_mod_cast deadline)

end
end ComplexityOfGenerators.ExpectedOriginalStarSampling
