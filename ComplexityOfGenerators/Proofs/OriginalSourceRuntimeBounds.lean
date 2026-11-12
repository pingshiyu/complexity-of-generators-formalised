import ComplexityOfGenerators.Foundations.FreshStreamSamplers
import ComplexityOfGenerators.Foundations.ResourceBounds

/-! A quadratic bounded-controller cost and a linear original-source cost
require a retry second moment and source first moments, respectively. -/
namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace FreshStreamSampler
variable {A : Type} [MeasurableSpace A] [MeasurableSingletonClass A] [Countable A]

theorem linear_source_cost (sampler : FreshStreamSampler A) (attempts sourceCost : A → ℕ)
    (outer call overhead secondMoment sourceMean : ℕ)
    (outerBound : (∫⁻ stream,(((attempts (sampler.run stream).1+1 : ℕ) : ℝ≥0∞)^2)
      ∂fairCoinMeasure)≤(secondMoment : ℝ≥0∞))
    (sourceBound : (∫⁻ stream,(sourceCost (sampler.run stream).1 : ℝ≥0∞)
      ∂fairCoinMeasure)≤(sourceMean : ℝ≥0∞)) :
    (∫⁻ stream,((outer*(attempts (sampler.run stream).1+1)^2+
      call*(sourceCost (sampler.run stream).1+overhead) : ℕ) : ℝ≥0∞)∂fairCoinMeasure)≤
        ((outer*secondMoment+call*(sourceMean+overhead) : ℕ) : ℝ≥0∞) := by
  let a : BitStream → ℝ≥0∞ := fun stream => ((attempts (sampler.run stream).1 : ℝ≥0∞)+1)^2
  let b : BitStream → ℝ≥0∞ := fun stream => (sourceCost (sampler.run stream).1 : ℝ≥0∞)
  have am : Measurable a := (measurable_of_countable (fun result : A => ((attempts result : ℝ≥0∞)+1)^2)).comp (measurable_fst.comp sampler.measurable)
  have bm : Measurable b := (measurable_of_countable (fun result : A => (sourceCost result : ℝ≥0∞))).comp (measurable_fst.comp sampler.measurable)
  have outerBound' : (∫⁻ stream,a stream∂fairCoinMeasure)≤(secondMoment : ℝ≥0∞) := by
    simpa only [a,Nat.cast_add,Nat.cast_one] using outerBound
  simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_pow,Nat.cast_one]
  change (∫⁻ stream,(outer : ℝ≥0∞)*a stream+(call : ℝ≥0∞)*(b stream+overhead)∂fairCoinMeasure)≤_
  have scaledAm : Measurable (fun stream => (outer : ℝ≥0∞)*a stream) := measurable_const.mul am
  have addedBm : Measurable (fun stream => b stream+(overhead : ℝ≥0∞)) := bm.add measurable_const
  rw [lintegral_add_left scaledAm,lintegral_const_mul _ am,
    lintegral_const_mul _ addedBm,lintegral_add_left bm]
  simp only [lintegral_const,measure_univ,mul_one]
  exact add_le_add (mul_le_mul' le_rfl outerBound')
    (mul_le_mul' le_rfl (add_le_add sourceBound (le_refl (overhead : ℝ≥0∞))))
end FreshStreamSampler

namespace OriginalSourceClosure

def expectedClock (outer call source : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (32*outer.asPolynomial+
    call.asPolynomial*((Polynomial.X+2)*source.asPolynomial+Polynomial.X+3))

theorem expectedClock_lower (outer call source : PolynomialBound) (n : ℕ) :
    32*outer n+call n*((n+2)*source n+n+3)≤expectedClock outer call source n := by
  have lower := PolynomialBound.eval_le_ofPolynomial
    (32*outer.asPolynomial+call.asPolynomial*((Polynomial.X+2)*source.asPolynomial+Polynomial.X+3)) n
  change _≤expectedClock outer call source n at lower
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,
    Polynomial.eval_ofNat,PolynomialBound.asPolynomial_eval] at lower
  exact lower


end OriginalSourceClosure
end
end ComplexityOfGenerators
