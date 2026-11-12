import ComplexityOfGenerators.Proofs.ExpectedOriginalStarSampling.Basic
import ComplexityOfGenerators.Proofs.OriginalSourceFamilySampler.Trace

/-! The chosen path, original native source runs and cumulative random
offsets describe one execution of one fair stream. -/
namespace ComplexityOfGenerators.ExpectedOriginalStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j,(G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))

theorem draw_trace_ae (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    ∀ᵐ stream∂fairCoinMeasure,
      let outcome := ((draw G p expected n available).run stream).1
      let parts := ExpectedStarSampling.chosenParts G p n (List.ofFn outcome.1.2)
      (∀ k<outcome.1.1,CertifiedStarPhase.value G.machine p n
        (List.ofFn (fixedBlock (StarCertification.width p n) stream k))=none) ∧
      CertifiedStarPhase.value G.machine p n
        (List.ofFn (fixedBlock (StarCertification.width p n) stream outcome.1.1))=
          some (StarPaths.payload parts) ∧
      CertifiedStarPhase.AvailableComposition G n parts ∧
      OriginalSourceFamilySampler.StreamTrace (families G)
        (fun i => stream (outerOffset outcome+i))
        (requests G p n (List.ofFn outcome.1.2)) outcome.2 := by
  let outer := ExpectedStarSampling.outerCall G p expected n available
  have traces : ∀ᵐ future∂fairCoinMeasure,∀ record : ExpectedStarSampling.OuterRecord p n,
      OriginalSourceFamilySampler.StreamTrace (families G) future
        (requests G p n (List.ofFn record.2))
        ((OriginalSourceFamilySampler.calls (families G) (requests G p n (List.ofFn record.2))
          (requests_active G p n (List.ofFn record.2))).run future).1 := by
    apply ae_all_iff.mpr
    intro record
    exact OriginalSourceFamilySampler.calls_trace_ae (families G) _ _
  have fresh := outer.tail_ae traces
  filter_upwards [ExpectedStarSampling.outerCall_success_ae G p expected n available,fresh]
    with stream success allTraces
  let record := (outer.run stream).1
  let records := ((OriginalSourceFamilySampler.calls (families G) (requests G p n (List.ofFn record.2))
    (requests_active G p n (List.ofFn record.2))).run (outer.run stream).2).1
  have selected := ExpectedStarSampling.chosenParts_spec G p n (List.ofFn record.2) success
  change (∀ k<record.1,CertifiedStarPhase.value G.machine p n
    (List.ofFn (fixedBlock (StarCertification.width p n) stream k))=none) ∧
      CertifiedStarPhase.value G.machine p n
        (List.ofFn (fixedBlock (StarCertification.width p n) stream record.1))=
          some (StarPaths.payload (ExpectedStarSampling.chosenParts G p n (List.ofFn record.2))) ∧
      CertifiedStarPhase.AvailableComposition G n (ExpectedStarSampling.chosenParts G p n (List.ofFn record.2)) ∧
      OriginalSourceFamilySampler.StreamTrace (families G)
        (fun i => stream ((record.1+1)*StarCertification.width p n+i))
        (requests G p n (List.ofFn record.2)) records
  refine ⟨ExpectedStarSampling.outerCall_failed G p expected n available stream,?_,selected.1,?_⟩
  · have same := ExpectedStarSampling.outerCall_block G p expected n available stream
    change record.2=fixedBlock (StarCertification.width p n) stream record.1 at same
    simpa only [← same] using selected.2
  · have remaining := allTraces record
    change OriginalSourceFamilySampler.StreamTrace (families G) (outer.run stream).2
      (requests G p n (List.ofFn record.2)) records at remaining
    rw [ExpectedStarSampling.outerCall_tail] at remaining
    exact remaining

theorem draw_tail (n : ℕ) (available : ExpectedStarSampling.Available G n) (stream : BitStream) :
    ((draw G p expected n available).run stream).2=
      fun i => stream (outerOffset (((draw G p expected n available).run stream).1)+
        sourceCoins (((draw G p expected n available).run stream).1)+i) := by
  unfold draw
  simp only [FreshStreamSampler.bind,FreshStreamSampler.map]
  rw [OriginalSourceFamilySampler.calls_tail]
  simp only [ExpectedStarSampling.outerCall_tail,outerOffset,sourceCoins,Nat.add_assoc]

theorem draw_native_prefix_ae (n : ℕ) (available : ExpectedStarSampling.Available G n) :
    ∀ᵐ stream∂fairCoinMeasure,
      let outcome := ((draw G p expected n available).run stream).1
      OriginalSourceFamilySampler.FiniteSequenceTrace (families G)
        (streamPrefix stream (outerOffset outcome+sourceCoins outcome)) (outerOffset outcome)
        (requests G p n (List.ofFn outcome.1.2)) outcome.2 := by
  filter_upwards [draw_trace_ae G p expected n available] with stream trace
  exact trace.2.2.2.native_prefix (families G) stream _ _ _ _ le_rfl

end
end ComplexityOfGenerators.ExpectedOriginalStarSampling
