import ComplexityOfGenerators.Proofs.ExpectedStarSampler

namespace ComplexityOfGenerators.ExpectedStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))

theorem outerCall_block (n : ℕ) (available : Available G n) (stream : BitStream) :
    ((outerCall G p expected n available).run stream).1.2 = fixedBlock (StarCertification.width p n) stream
      ((outerCall G p expected n available).run stream).1.1 := rfl

theorem outerCall_tail (n : ℕ) (available : Available G n) (stream : BitStream) :
    ((outerCall G p expected n available).run stream).2 =
      fun i => stream ((((outerCall G p expected n available).run stream).1.1+1)*StarCertification.width p n+i) := rfl

theorem outerCall_failed (n : ℕ) (available : Available G n) (stream : BitStream) (k : ℕ)
    (earlier : k < ((outerCall G p expected n available).run stream).1.1) :
    CertifiedStarPhase.value G.machine p n (List.ofFn (fixedBlock (StarCertification.width p n) stream k)) = none := by
  have absent : fixedBlock (StarCertification.width p n) stream k ∉ successSet G p n := by
    rcases firstSuccessIndex_spec (StarCertification.width p n) (successSet G p n) stream with ⟨_,first⟩ | ⟨_,never⟩
    · exact first k earlier
    · exact never k
  cases value : CertifiedStarPhase.value G.machine p n
      (List.ofFn (fixedBlock (StarCertification.width p n) stream k)) with
  | none => rfl
  | some word => exact False.elim (absent (by simp [successSet,value]))

theorem outerCall_success_ae (n : ℕ) (available : Available G n) :
    ∀ᵐ stream ∂fairCoinMeasure, (CertifiedStarPhase.value G.machine p n
      (List.ofFn ((outerCall G p expected n available).run stream).1.2)).isSome = true := by
  exact firstSuccessIndex_ae_success (StarCertification.width p n) ((StarCertification.width p).positive n)
    (successSet G p n) (Set.to_countable _ |>.measurableSet)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ≥0∞) < 1/2) (success_mass G p expected n available))

variable (P : BoundedPhaseFamily α) (layers : ∀ n, P.layer n = G.layer n)

/-- The outer retries and subsequent source records describe the same
single fair-stream execution as the native generator. The unread suffix after
path selection is fresh even though its position is random. -/
theorem draw_trace_ae (n : ℕ) (available : Available G n) :
    ∀ᵐ stream ∂fairCoinMeasure,
      let outcome := ((draw G p expected P layers n available).run stream).1
      let parts := chosenParts G p n (List.ofFn outcome.1.2)
      (∀ k < outcome.1.1, CertifiedStarPhase.value G.machine p n
        (List.ofFn (fixedBlock (StarCertification.width p n) stream k)) = none) ∧
      CertifiedStarPhase.value G.machine p n
        (List.ofFn (fixedBlock (StarCertification.width p n) stream outcome.1.1)) = some (StarPaths.payload parts) ∧
      CertifiedStarPhase.AvailableComposition G n parts ∧
      P.StreamTrace (fun i => stream ((outcome.1.1+1)*StarCertification.width p n+i))
        parts (BoundedPhaseFamily.nativeRecords outcome.2) := by
  let outer := outerCall G p expected n available
  have traces : ∀ᵐ future ∂fairCoinMeasure, ∀ record : OuterRecord p n,
      P.StreamTrace future (chosenParts G p n (List.ofFn record.2))
        (BoundedPhaseFamily.nativeRecords
          ((P.recordCalls (chosenParts G p n (List.ofFn record.2))
            (chosenParts_sourceActive G p P layers n record)).run future).1) := by
    apply ae_all_iff.mpr
    intro record
    exact P.recordCalls_trace_ae _ _
  have fresh := outer.tail_ae traces
  filter_upwards [outerCall_success_ae G p expected n available,fresh] with stream success allTraces
  let record := (outer.run stream).1
  let parts := chosenParts G p n (List.ofFn record.2)
  let records := BoundedPhaseFamily.nativeRecords
    ((P.recordCalls parts (chosenParts_sourceActive G p P layers n record)).run (outer.run stream).2).1
  have selected := chosenParts_spec G p n (List.ofFn record.2) success
  change (∀ k < record.1, CertifiedStarPhase.value G.machine p n
    (List.ofFn (fixedBlock (StarCertification.width p n) stream k)) = none) ∧
      CertifiedStarPhase.value G.machine p n
        (List.ofFn (fixedBlock (StarCertification.width p n) stream record.1)) = some (StarPaths.payload parts) ∧
      CertifiedStarPhase.AvailableComposition G n parts ∧
      P.StreamTrace (fun i => stream ((record.1+1)*StarCertification.width p n+i)) parts records
  refine ⟨outerCall_failed G p expected n available stream,?_,selected.1,?_⟩
  · have same := outerCall_block G p expected n available stream
    change record.2 = fixedBlock (StarCertification.width p n) stream record.1 at same
    simpa only [← same] using selected.2
  · have remaining := allTraces record
    change P.StreamTrace ((outerCall G p expected n available).run stream).2 parts records at remaining
    rw [outerCall_tail] at remaining
    exact remaining

end
end ComplexityOfGenerators.ExpectedStarSampling
