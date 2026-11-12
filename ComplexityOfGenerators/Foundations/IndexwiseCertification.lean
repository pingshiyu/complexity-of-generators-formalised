import ComplexityOfGenerators.Foundations.ExpectedClosureBounds
import ComplexityOfGenerators.Foundations.FreshBits
import ComplexityOfGenerators.Simulation.UnionGenerator.Views

/-! One bounded test per source index suffices for star certification. Giving
index j a quadratic error budget makes the errors summable uniformly in the
outer target; the test needs no access to that outer target. Its outputs are
discarded before the fresh generation calls. -/
namespace ComplexityOfGenerators.IndexwiseCertification
open MeasureTheory Simulation
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

private def weight : PolynomialBound := ⟨16, 2, by decide⟩
def clock (p : PolynomialBound) : PolynomialBound := weight.mul p
noncomputable def seed (p : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial ((clock p).asPolynomial+1)

theorem seed_fits (p : PolynomialBound) (n : ℕ) : clock p n+1 ≤ seed p n := by
  have lower := PolynomialBound.eval_le_ofPolynomial ((clock p).asPolynomial+1) n
  simpa only [seed, Polynomial.eval_add, Polynomial.eval_one, PolynomialBound.asPolynomial_eval] using lower

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

def accepts (p : PolynomialBound) (n : ℕ) (bits : Fin (seed p n) → Bool) : Bool :=
  (UnionGenerator.sourceValue M (clock p) n (List.ofFn bits)).isSome

theorem accepts_iff (p : PolynomialBound) (n : ℕ) (bits : Fin (seed p n) → Bool) :
    accepts M p n bits = true ↔ ∃ word,
      M.run (generatorData n) (List.ofFn bits) (clock p n) = .halted (.accepted word) := by
  unfold accepts UnionGenerator.sourceValue
  cases execution : M.run (generatorData n) (List.ofFn bits) (clock p n) with
  | running configuration => simp [RunState.acceptedWord]
  | halted result => cases result <;> simp [RunState.acceptedWord, Outcome.acceptedWord]

private theorem runtime_ratio (p : PolynomialBound) (n : ℕ) :
    (p n : ℝ≥0∞)/(clock p n : ℝ≥0∞) = ((weight n : ℕ) : ℝ≥0∞)⁻¹ := by
  rw [clock, PolynomialBound.mul_eval, Nat.cast_mul, div_eq_mul_inv,
    ENNReal.mul_inv (Or.inl (by exact_mod_cast (weight.positive n).ne')) (Or.inl (by simp))]
  have nonzero : (p n : ℝ≥0∞) ≠ 0 := by exact_mod_cast (p.positive n).ne'
  calc
    _ = ((p n : ℝ≥0∞)*(p n : ℝ≥0∞)⁻¹)*(weight n : ℝ≥0∞)⁻¹ := by ac_rfl
    _ = _ := by rw [ENNReal.mul_inv_cancel nonzero (by simp), one_mul]

/-- This is a bound for an actual capped native run on a fixed finite block.
The source contributes only its expected-runtime bound. -/
theorem acceptance_lower_bound (p : PolynomialBound) (n : ℕ)
    (expected : M.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) :
    1-((16*(n+1)^2 : ℕ) : ℝ≥0∞)⁻¹ ≤
      fairBlockMeasure (seed p n) {bits | accepts M p n bits} := by
  have initial := M.bounded_prefix_acceptance_lower_bound (generatorData n) (p n : ℝ≥0∞)
    (clock p n) ((clock p).positive n) expected
  rw [runtime_ratio] at initial
  have extend : {stream | ∃ word, M.run (generatorData n)
      (streamPrefix stream (clock p n+1)) (clock p n) = .halted (.accepted word)} ⊆
      {stream | ∃ word, M.run (generatorData n)
        (streamPrefix stream (seed p n)) (clock p n) = .halted (.accepted word)} := by
    intro stream member
    obtain ⟨word, run⟩ := member
    refine ⟨word, ?_⟩
    rw [M.run_streamPrefix_eq_of_not_exhausted (generatorData n)
      (stream_mem_prefix_cylinder stream (clock p n+1)) (by have := seed_fits p n; omega) (by simp [run]), run]
  have finiteMeasurable : MeasurableSet {bits | accepts M p n bits} := Set.to_countable _ |>.measurableSet
  have law := fairCoinMeasure_prefix_tail (seed p n) {bits | accepts M p n bits} Set.univ finiteMeasurable MeasurableSet.univ
  simp only [Set.mem_univ, and_true, measure_univ, mul_one] at law
  have event : {stream | (splitStream (seed p n) stream).1 ∈ {bits | accepts M p n bits}} =
      {stream | ∃ word, M.run (generatorData n)
        (streamPrefix stream (seed p n)) (clock p n) = .halted (.accepted word)} := by
    ext stream
    exact accepts_iff M p n (splitStream (seed p n) stream).1
  rw [event] at law
  change 1-(weight n : ℝ≥0∞)⁻¹ ≤ _
  exact (initial.trans (measure_mono extend)).trans_eq law

theorem failure_upper_bound (p : PolynomialBound) (n : ℕ)
    (expected : M.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) :
    fairBlockMeasure (seed p n) {bits | accepts M p n bits = false} ≤
      ((16*(n+1)^2 : ℕ) : ℝ≥0∞)⁻¹ := by
  have lower := acceptance_lower_bound M p n expected
  have failed : {bits | accepts M p n bits = false} = {bits | accepts M p n bits}ᶜ := by
    ext bits
    simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, Bool.eq_false_iff]
  rw [failed, measure_compl (Set.to_countable _ |>.measurableSet) (measure_ne_top _ _), measure_univ]
  exact (tsub_le_iff_right).mpr (by simpa only [add_comm] using (tsub_le_iff_right).mp lower)

end
end ComplexityOfGenerators.IndexwiseCertification
