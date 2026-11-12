import ComplexityOfGenerators.Proofs.ExpectedStarSampleTrace

namespace ComplexityOfGenerators.ExpectedStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

abbrev DrawResult (p : PolynomialBound) (n : ℕ) (α : Type) := OuterRecord p n × List (ℕ × List α)

def outputWord {p : PolynomialBound} {n : ℕ} (result : DrawResult p n α) : List α :=
  ExpectedStarCalls.words (BoundedPhaseFamily.nativeRecords result.2)
def outerAttempts {p : PolynomialBound} {n : ℕ} (result : DrawResult p n α) : ℕ := result.1.1+1
def innerAttempts {p : PolynomialBound} {n : ℕ} (result : DrawResult p n α) : ℕ :=
  ExpectedStarCalls.blocks (BoundedPhaseFamily.nativeRecords result.2)
def totalAttempts {p : PolynomialBound} {n : ℕ} (result : DrawResult p n α) : ℕ :=
  outerAttempts result+innerAttempts result+1

variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))

include expected in
theorem outerCall_secondMoment (n : ℕ) (available : Available G n) :
    (∫⁻ stream, ((((outerCall G p expected n available).run stream).1.1+1 : ℕ) : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤ 8 := by
  have mass := success_mass G p expected n available
  have inverse : (fairBlockMeasure (StarCertification.width p n) (successSet G p n))⁻¹ ≤ (2 : ℝ≥0∞) := by
    simpa only [one_div,inv_inv] using ENNReal.inv_le_inv.mpr mass
  have initial := firstSuccessIndex_secondMoment_le (StarCertification.width p n)
    ((StarCertification.width p).positive n) (successSet G p n) (Set.to_countable _ |>.measurableSet)
  change (∫⁻ stream, ((((outerCall G p expected n available).run stream).1.1+1 : ℕ) : ℝ≥0∞)^2 ∂fairCoinMeasure) ≤ _ at initial
  apply initial.trans
  rw [div_eq_mul_inv,ENNReal.inv_pow]
  calc
    _ ≤ 2*(2 : ℝ≥0∞)^2 := mul_le_mul' le_rfl (pow_le_pow_left' inverse 2)
    _ = 8 := by norm_num

include expected in
theorem outerCall_live (n : ℕ) (available : Available G n) :
    ∀ᵐ record ∂(outerCall G p expected n available).distribution,
      (CertifiedStarPhase.value G.machine p n (List.ofFn record.2)).isSome = true := by
  let predicate : OuterRecord p n → Prop := fun record =>
    (CertifiedStarPhase.value G.machine p n (List.ofFn record.2)).isSome = true
  have measurable : MeasurableSet {record | predicate record} := Set.to_countable _ |>.measurableSet
  exact ((outerCall G p expected n available).distribution_ae_iff predicate measurable).mpr
    (outerCall_success_ae G p expected n available)

variable (P : BoundedPhaseFamily α) (layers : ∀ n, P.layer n = G.layer n)

theorem draw_lintegral (n : ℕ) (available : Available G n) (value : DrawResult p n α → ℝ≥0∞) :
    (∫⁻ stream, value (((draw G p expected P layers n available).run stream).1) ∂fairCoinMeasure) =
      ∫⁻ record, ∫⁻ future, value (record,
        ((P.recordCalls (chosenParts G p n (List.ofFn record.2))
          (chosenParts_sourceActive G p P layers n record)).run future).1) ∂fairCoinMeasure
        ∂(outerCall G p expected n available).distribution := by
  exact FreshStreamSampler.lintegral_bind (outerCall G p expected n available)
    (fun record => (P.recordCalls (chosenParts G p n (List.ofFn record.2))
      (chosenParts_sourceActive G p P layers n record)).map (fun records => (record,records)) (measurable_of_countable _))
    value (measurable_of_countable _)

/-- The actual composite sample has target mean n. Conditional means are n
for every successfully selected composition, so the outer selection cannot
bias the expected output length. -/
theorem draw_word_mean (n : ℕ) (available : Available G n) :
    (∫⁻ stream, (outputWord (((draw G p expected P layers n available).run stream).1)).length
      ∂fairCoinMeasure) = (n : ℝ≥0∞) := by
  rw [draw_lintegral G p expected P layers n available (fun result => (outputWord result).length)]
  have each (record : OuterRecord p n) :
      (∫⁻ future, (outputWord (record,
        ((P.recordCalls (chosenParts G p n (List.ofFn record.2))
          (chosenParts_sourceActive G p P layers n record)).run future).1)).length ∂fairCoinMeasure) =
        ((chosenParts G p n (List.ofFn record.2)).sum : ℝ≥0∞) :=
    P.factorCalls_mean _ _
  simp_rw [each]
  have live := outerCall_live G p expected n available
  calc
    _ = ∫⁻ _record, (n : ℝ≥0∞) ∂(outerCall G p expected n available).distribution := by
      apply lintegral_congr_ae
      filter_upwards [live] with record accepted
      exact congrArg (fun k : ℕ => (k : ℝ≥0∞)) (chosenParts_spec G p n (List.ofFn record.2) accepted).1.1
    _ = _ := by simp

theorem draw_inner_secondMoment (n : ℕ) (available : Available G n) :
    (∫⁻ stream, (innerAttempts (((draw G p expected P layers n available).run stream).1) : ℝ≥0∞)^2
      ∂fairCoinMeasure) ≤ 2*(n : ℝ≥0∞)^2*(P.reciprocal n : ℝ≥0∞)^2 := by
  rw [draw_lintegral G p expected P layers n available (fun result => (innerAttempts result : ℝ≥0∞)^2)]
  calc
    _ ≤ ∫⁻ _record, 2*(n : ℝ≥0∞)^2*(P.reciprocal n : ℝ≥0∞)^2
        ∂(outerCall G p expected n available).distribution := by
      apply lintegral_mono
      intro record
      have bounds := chosenParts_bounds G p n (List.ofFn record.2)
      exact P.factorCalls_secondMoment _ _ n bounds.2 bounds.1
    _ = _ := by simp

theorem draw_outer_secondMoment (n : ℕ) (available : Available G n) :
    (∫⁻ stream, (outerAttempts (((draw G p expected P layers n available).run stream).1) : ℝ≥0∞)^2
      ∂fairCoinMeasure) ≤ 8 := by
  rw [draw_lintegral G p expected P layers n available (fun result => (outerAttempts result : ℝ≥0∞)^2)]
  simp only [outerAttempts,lintegral_const,measure_univ,mul_one]
  have measurable : Measurable (fun stream => ((outerCall G p expected n available).run stream).1) :=
    measurable_fst.comp (outerCall G p expected n available).measurable
  change (∫⁻ record, ((record.1+1 : ℕ) : ℝ≥0∞)^2
    ∂fairCoinMeasure.map (fun stream => ((outerCall G p expected n available).run stream).1)) ≤ _
  rw [lintegral_map (measurable_of_countable _) measurable]
  exact outerCall_secondMoment G p expected n available

end
end ComplexityOfGenerators.ExpectedStarSampling
