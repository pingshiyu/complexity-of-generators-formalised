import ComplexityOfGenerators.Proofs.ExpectedStarSampleCost
import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.Native

namespace ComplexityOfGenerators.ExpectedStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ExpectedStarGenerator.machine
variable {α : Type} [Fintype α]

private theorem prefix_block (stream : BitStream) (total width k : ℕ) (fits : (k+1)*width ≤ total) :
    ((streamPrefix stream total).drop (k*width)).take width = List.ofFn (fixedBlock width stream k) := by
  change _ = List.ofFn (fun index : Fin width => stream (k*width+index.val))
  exact BalancedPairPhase.streamPrefix_drop_take stream total (k*width) width (by nlinarith)

variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))
    (P : BoundedPhaseFamily α) (layers : ∀ n, P.layer n = G.layer n)

/-- The fair-stream sample is an actual accepting execution of the compiled
finite machine, with the proved quadratic native deadline. -/
theorem native_stream_execution_ae (n : ℕ) (available : Available G n) :
    ∀ᵐ stream ∂fairCoinMeasure,
      let sample := ((draw G p expected P layers n available).run stream).1
      (ExpectedStarGenerator.machine G.machine p P).streamProduces (generatorData n) stream (outputWord sample) ∧
      (ExpectedStarGenerator.machine G.machine p P).streamRuntime (generatorData n) stream ≤
        ((25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P n)^2*(totalAttempts sample+1)^2 : ℕ) : ℝ≥0∞) := by
  filter_upwards [draw_trace_ae G p expected P layers n available] with stream trace
  let sample := ((draw G p expected P layers n available).run stream).1
  let parts := chosenParts G p n (List.ofFn sample.1.2)
  let records := BoundedPhaseFamily.nativeRecords sample.2
  let offset := (sample.1.1+1)*StarCertification.width p n
  let total := offset+ExpectedStarCalls.consumed P parts records
  let bits := streamPrefix stream total
  rcases trace with ⟨failed,accepted,productive,inner⟩
  have enough : offset ≤ bits.length := by simp only [bits,streamPrefix_length,total]; omega
  have failedPrefix (k : ℕ) (earlier : k < sample.1.1) :
      CertifiedStarPhase.value G.machine p n
        ((bits.drop (k*StarCertification.width p n)).take (StarCertification.width p n)) = none := by
    have fits : (k+1)*StarCertification.width p n ≤ total := by
      apply (Nat.mul_le_mul_right _ (show k+1 ≤ sample.1.1+1 by omega)).trans
      change offset ≤ total
      omega
    change CertifiedStarPhase.value G.machine p n
      (((streamPrefix stream total).drop (k*StarCertification.width p n)).take (StarCertification.width p n)) = none
    rw [prefix_block stream total (StarCertification.width p n) k fits]
    exact failed k earlier
  have acceptedPrefix : CertifiedStarPhase.value G.machine p n
      ((bits.drop (sample.1.1*StarCertification.width p n)).take (StarCertification.width p n)) =
        some (StarPaths.payload parts) := by
    change CertifiedStarPhase.value G.machine p n
      (((streamPrefix stream total).drop (sample.1.1*StarCertification.width p n)).take (StarCertification.width p n)) = _
    rw [prefix_block stream total (StarCertification.width p n) sample.1.1 (by change offset ≤ total; omega)]
    exact accepted
  have innerPrefix : ExpectedStarCalls.Trace P bits offset parts records :=
    BoundedPhaseFamily.StreamTrace.native_prefix P stream total offset parts records inner le_rfl
  obtain ⟨ticks,timeBound,run⟩ := ExpectedStarGenerator.machine_runs_trace G.machine p P n sample.1.1 parts records bits
    productive.1 (fun j member => (productive.2 j member).1) enough failedPrefix acceptedPrefix innerPrefix
  have run' : (ExpectedStarGenerator.machine G.machine p P).run (generatorData n) bits ticks =
      .halted (.accepted (outputWord sample)) := run
  have cylinder : stream ∈ cylinder bits := stream_mem_prefix_cylinder stream total
  have nativeByTime : (ExpectedStarGenerator.machine G.machine p P).streamAcceptsBy (generatorData n) stream ticks :=
    ⟨bits,outputWord sample,cylinder,run'⟩
  have upper : ticks ≤ 25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P n)^2*(totalAttempts sample+1)^2 := by
    apply timeBound.trans
    change 25*(ExpectedStarGenerator.primitiveCoefficient G.machine p P n)^2*(totalAttempts sample)^2 ≤ _
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.le_succ _) 2)
  exact ⟨⟨bits,cylinder,ticks,run'⟩,
    ((ExpectedStarGenerator.machine G.machine p P).streamRuntime_le_of_acceptsBy (generatorData n) nativeByTime).trans
      (by exact_mod_cast upper)⟩

end
end ComplexityOfGenerators.ExpectedStarSampling
