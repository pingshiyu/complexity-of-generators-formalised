import ComplexityOfGenerators.Foundations.StreamSemantics

/-! A finite supported output has a cylinder of positive measure. Almost-sure
stream semantics therefore determines support even at exceptional streams. -/
namespace ComplexityOfGenerators.Machine
open MeasureTheory
open scoped ENNReal
noncomputable section
variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

theorem generatedLanguage_subset_of_ae_streamProduces (L : Set (List O))
    (outputs : ∀ᵐ stream∂fairCoinMeasure,∃ word∈L,M.streamProduces data stream word) :
    M.generatedLanguage data⊆L := by
  rintro word ⟨bits,nonempty,produces⟩
  by_contra outside
  have null : fairCoinMeasure {stream | ¬∃ value∈L,M.streamProduces data stream value}=0 := ae_iff.mp outputs
  have subset : cylinder bits⊆{stream | ¬∃ value∈L,M.streamProduces data stream value} := by
    intro stream member ⟨value,valid,produced⟩
    have equal := M.streamProduces_unique data (show M.streamProduces data stream word from ⟨bits,member,produces⟩) produced
    exact outside (equal.symm ▸ valid)
  have positive : 0<fairCoinMeasure (cylinder bits) := by
    rw [fairCoinMeasure_cylinder]
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
  have bound : fairCoinMeasure (cylinder bits)≤
      fairCoinMeasure {stream | ¬∃ value∈L,M.streamProduces data stream value} := measure_mono subset
  rw [null] at bound
  exact not_lt_of_ge bound positive

/-- Almost-sure concrete stream executions give productive measure one. -/
theorem acceptedStreams_measure_one_of_ae_streamProduces (output : BitStream → List O)
    (paths : ∀ᵐ stream∂fairCoinMeasure,M.streamProduces data stream (output stream)) :
    fairCoinMeasure (M.acceptedStreams data)=1 := by
  have accepted : ∀ᵐ stream∂fairCoinMeasure,stream∈M.acceptedStreams data := by
    filter_upwards [paths] with stream produced
    obtain ⟨bits,member,run⟩ := produced
    exact ⟨bits,member,output stream,run⟩
  have null : fairCoinMeasure (M.acceptedStreams data)ᶜ=0 := ae_iff.mp accepted
  have sum := measure_add_measure_compl (μ:=fairCoinMeasure) (M.measurableSet_acceptedStreams data)
  rw [null,add_zero,measure_univ] at sum
  exact sum

/-- Stream-output equality identifies the actual native expected length. -/
theorem expectedLength_eq_of_ae_streamProduces (output : BitStream → List O)
    (paths : ∀ᵐ stream∂fairCoinMeasure,M.streamProduces data stream (output stream)) :
    M.expectedLength data=∫⁻ stream,((output stream).length : ℝ≥0∞)∂fairCoinMeasure := by
  apply lintegral_congr_ae
  filter_upwards [paths] with stream produced
  exact congrArg (fun n : ℕ => (n : ℝ≥0∞)) (M.streamLength_of_produces data produced)

end
end ComplexityOfGenerators.Machine
