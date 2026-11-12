import ComplexityOfGenerators.Proofs.ExpectedStarSampleMoments

namespace ComplexityOfGenerators.ExpectedStarSampling
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

private theorem charged_square_le (a b : ℕ) : (a+b+2)^2 ≤ 3*(a^2+b^2+4) := by
  have cauchy := finite_sum_square_le 3 (fun i : Fin 3 => if i.val = 0 then a else if i.val = 1 then b else 2)
  simpa [Fin.sum_univ_succ,Nat.add_assoc] using cauchy

variable {α : Type} [Fintype α]
variable (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ j, (G.layer j).Nonempty → G.machine.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞))
    (P : BoundedPhaseFamily α) (layers : ∀ n, P.layer n = G.layer n)

/-- One final quadratic compiler is paid for by the second moments of the
actual outer and inner retry counts, without a variance assumption on the
original source's runtime or on its output length. -/
theorem draw_charged_secondMoment (n : ℕ) (available : Available G n) :
    (∫⁻ stream, (((totalAttempts (((draw G p expected P layers n available).run stream).1)+1 : ℕ) : ℝ≥0∞)^2)
      ∂fairCoinMeasure) ≤ 36+6*(n : ℝ≥0∞)^2*(P.reciprocal n : ℝ≥0∞)^2 := by
  let sampler := draw G p expected P layers n available
  let a : BitStream → ℝ≥0∞ := fun stream => (outerAttempts (sampler.run stream).1 : ℝ≥0∞)^2
  let b : BitStream → ℝ≥0∞ := fun stream => (innerAttempts (sampler.run stream).1 : ℝ≥0∞)^2
  have am : Measurable a := (measurable_of_countable (fun result : DrawResult p n α =>
    (outerAttempts result : ℝ≥0∞)^2)).comp (measurable_fst.comp sampler.measurable)
  have bm : Measurable b := (measurable_of_countable (fun result : DrawResult p n α =>
    (innerAttempts result : ℝ≥0∞)^2)).comp (measurable_fst.comp sampler.measurable)
  have first : (∫⁻ stream, a stream ∂fairCoinMeasure) ≤ 8 := draw_outer_secondMoment G p expected P layers n available
  have second : (∫⁻ stream, b stream ∂fairCoinMeasure) ≤
      2*(n : ℝ≥0∞)^2*(P.reciprocal n : ℝ≥0∞)^2 := draw_inner_secondMoment G p expected P layers n available
  calc
    _ ≤ ∫⁻ stream, 3*(a stream+b stream+4) ∂fairCoinMeasure := by
      apply lintegral_mono
      intro stream
      have natural := charged_square_le (outerAttempts (sampler.run stream).1) (innerAttempts (sampler.run stream).1)
      have casted : ((((outerAttempts (sampler.run stream).1+innerAttempts (sampler.run stream).1+2)^2 : ℕ)) : ℝ≥0∞) ≤
          ((3*(outerAttempts (sampler.run stream).1^2+innerAttempts (sampler.run stream).1^2+4) : ℕ) : ℝ≥0∞) := by
        exact_mod_cast natural
      simpa [a,b,sampler,totalAttempts,Nat.cast_pow,Nat.cast_mul,Nat.cast_add,Nat.cast_ofNat,add_assoc] using casted
    _ = 3*((∫⁻ stream, a stream ∂fairCoinMeasure)+(∫⁻ stream, b stream ∂fairCoinMeasure)+4) := by
      have sumMeasurable : Measurable (fun stream => a stream+b stream+4) := (am.add bm).add measurable_const
      have abMeasurable : Measurable (fun stream => a stream+b stream) := am.add bm
      rw [lintegral_const_mul _ sumMeasurable,lintegral_add_left abMeasurable,lintegral_add_left am]
      simp
    _ ≤ 3*(8+2*(n : ℝ≥0∞)^2*(P.reciprocal n : ℝ≥0∞)^2+4) := by gcongr
    _ = _ := by ring

end
end ComplexityOfGenerators.ExpectedStarSampling
