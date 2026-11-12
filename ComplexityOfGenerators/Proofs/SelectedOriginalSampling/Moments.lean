import ComplexityOfGenerators.Proofs.SelectedOriginalSampling.Basic

namespace ComplexityOfGenerators.SelectedOriginalSampling
open MeasureTheory
open scoped ENNReal
open OriginalSourceFamilySampler (Request)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} (families : Bool → UniformGenerators α) (width : PolynomialBound)
    (value : ℕ → BitString → Option (List Request))
    (sound : ∀ n bits requests,value n bits=some requests →
      ∀ entry∈requests,((families entry.1).layer entry.2).Nonempty)

theorem draw_word_mean (mean : ∀ tag,(families tag).ExpectedLength)
    (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n))
    (balanced : ∀ bits requests,value n bits=some requests → (requests.map Prod.snd).sum=n) :
    (∫⁻ stream,((outputWord families width (((draw families width value sound n positive).run stream).1)).length : ℝ≥0∞)
      ∂fairCoinMeasure)=(n : ℝ≥0∞) := by
  rw [draw_lintegral families width value sound n positive
    (fun result => ((outputWord families width result).length : ℝ≥0∞))]
  have each (record : OuterRecord width n) :
      (∫⁻ future,((outputWord families width (record,
        ((OriginalSourceFamilySampler.calls families (selected width value n record)
          (selected_active families width value sound n record)).run future).1)).length : ℝ≥0∞)∂fairCoinMeasure)=
        (((selected width value n record).map Prod.snd).sum : ℝ≥0∞) :=
    OriginalSourceFamilySampler.calls_word_mean families mean _ _
  simp_rw [each]
  calc
    _ = ∫⁻ _record,(n : ℝ≥0∞)∂(outer width value n positive).distribution := by
      apply lintegral_congr_ae
      filter_upwards [outer_live width value n positive] with record accepted
      obtain ⟨requests,found⟩ := Option.isSome_iff_exists.mp accepted
      simp only [selected,found,Option.getD_some]
      exact congrArg (fun k : ℕ => (k : ℝ≥0∞)) (balanced _ requests found)
    _ = _ := by simp

theorem draw_source_runtime_le (p : PolynomialBound)
    (expected : ∀ tag j,((families tag).layer j).Nonempty →
      (families tag).machine.expectedRuntime (generatorData j)≤(p j : ℝ≥0∞))
    (n : ℕ) (positive : 0<fairBlockMeasure (width n) (success width value n)) (count : ℕ)
    (bounds : ∀ bits requests,value n bits=some requests →
      requests.length≤count ∧ ∀ entry∈requests,entry.2≤n) :
    (∫⁻ stream,(sourceRuntime families width (((draw families width value sound n positive).run stream).1) : ℝ≥0∞)
      ∂fairCoinMeasure)≤(count : ℝ≥0∞)*(p n : ℝ≥0∞) := by
  rw [draw_lintegral families width value sound n positive
    (fun result => (sourceRuntime families width result : ℝ≥0∞))]
  calc
    _ ≤ ∫⁻ _record,(count : ℝ≥0∞)*(p n : ℝ≥0∞)∂(outer width value n positive).distribution := by
      apply lintegral_mono
      intro record
      have chosen : (selected width value n record).length≤count ∧
          ∀ entry∈selected width value n record,entry.2≤n := by
        cases found : value n (List.ofFn record.2) with
        | none => simp [selected,found]
        | some requests => simpa only [selected,found,Option.getD_some] using bounds _ requests found
      have initial := OriginalSourceFamilySampler.calls_runtime_le families p expected
        (selected width value n record) (selected_active families width value sound n record) n chosen.2
      exact initial.trans (mul_le_mul' (Nat.cast_le.mpr chosen.1) le_rfl)
    _ = _ := by simp

theorem draw_outer_secondMoment (n : ℕ)
    (positive : 0<fairBlockMeasure (width n) (success width value n)) (reciprocal : ℕ)
    (mass : (reciprocal : ℝ≥0∞)⁻¹≤fairBlockMeasure (width n) (success width value n)) :
    (∫⁻ stream,(((((draw families width value sound n positive).run stream).1.1.1+1 : ℕ) : ℝ≥0∞)^2)
      ∂fairCoinMeasure)≤2*(reciprocal : ℝ≥0∞)^2 := by
  rw [draw_lintegral families width value sound n positive (fun result => ((result.1.1+1 : ℕ) : ℝ≥0∞)^2)]
  simp only [lintegral_const,measure_univ,mul_one]
  have measurable : Measurable (fun stream => ((outer width value n positive).run stream).1) :=
    measurable_fst.comp (outer width value n positive).measurable
  change (∫⁻ record,((record.1+1 : ℕ) : ℝ≥0∞)^2∂fairCoinMeasure.map
    (fun stream => ((outer width value n positive).run stream).1))≤_
  rw [lintegral_map (measurable_of_countable _) measurable]
  have initial := firstSuccessIndex_secondMoment_le (width n) (width.positive n)
    (success width value n) (Set.to_countable _ |>.measurableSet)
  change (∫⁻ stream,(((((outer width value n positive).run stream).1.1+1 : ℕ) : ℝ≥0∞)^2)
    ∂fairCoinMeasure)≤_ at initial
  have inverse : (fairBlockMeasure (width n) (success width value n))⁻¹≤(reciprocal : ℝ≥0∞) := by
    simpa only [inv_inv] using ENNReal.inv_le_inv.mpr mass
  apply initial.trans
  rw [div_eq_mul_inv,ENNReal.inv_pow]
  exact mul_le_mul' le_rfl (pow_le_pow_left' inverse 2)

end
end ComplexityOfGenerators.SelectedOriginalSampling
