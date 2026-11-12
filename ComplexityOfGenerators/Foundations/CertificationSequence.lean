import ComplexityOfGenerators.Foundations.CertificationErrors
import ComplexityOfGenerators.Foundations.FreshStreamSequence
import ComplexityOfGenerators.ExpectedGenerators

/-! All active source indices can be certified with a constant probability
using one bounded run at each index. The tests read consecutive fresh blocks
of a single stream; no independent family of oracles is assumed. -/
namespace ComplexityOfGenerators.IndexwiseCertification
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

noncomputable def test (M : Machine Unit Bool α) (p : PolynomialBound) (n : ℕ) :
    FreshStreamSampler (ℕ × Bool) :=
  (FreshStreamSampler.readPrefix (seed p n)).map
    (fun bits => (n, accepts M p n bits)) (measurable_of_countable _)

noncomputable def tests (M : Machine Unit Bool α) (p : PolynomialBound) (count : ℕ) :=
  FreshStreamSampler.sequence (List.ofFn (fun i : Fin count => test M p (i+1)))

private def failed (G : UniformGenerators α) (result : ℕ × Bool) : ℝ≥0∞ :=
  by
    classical
    exact if (G.layer result.1).Nonempty ∧ result.2 = false then 1 else 0

private theorem test_failure_integral (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ n, (G.layer n).Nonempty →
      G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) (n : ℕ) :
    (∫⁻ stream, failed G ((test G.machine p n).run stream).1 ∂fairCoinMeasure) ≤
      ((16*(n+1)^2 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  by_cases active : (G.layer n).Nonempty
  · have hm : MeasurableSet {bits | accepts G.machine p n bits = false} :=
      Set.to_countable _ |>.measurableSet
    have law := fairCoinMeasure_prefix_tail (seed p n)
      {bits | accepts G.machine p n bits = false} Set.univ hm MeasurableSet.univ
    simp only [Set.mem_univ, Set.mem_ofPred_eq, and_true, measure_univ, mul_one] at law
    have measurable : MeasurableSet {stream | accepts G.machine p n
        (splitStream (seed p n) stream).1 = false} :=
      ((measurable_fst.comp (measurable_splitStream (seed p n))) hm)
    have integral : (∫⁻ stream, failed G ((test G.machine p n).run stream).1 ∂fairCoinMeasure) =
        fairCoinMeasure {stream | accepts G.machine p n
          (splitStream (seed p n) stream).1 = false} := by
      have form : (fun stream => failed G ((test G.machine p n).run stream).1) =
          ({stream | accepts G.machine p n (splitStream (seed p n) stream).1 = false}.indicator
            (fun _ => (1 : ℝ≥0∞))) := by
        funext stream
        simp [test, FreshStreamSampler.map, FreshStreamSampler.readPrefix, failed, active, Set.indicator]
      rw [form, lintegral_indicator_const measurable, one_mul]
    rw [integral, law]
    exact failure_upper_bound G.machine p n (expected n active)
  · simp [test, FreshStreamSampler.map, FreshStreamSampler.readPrefix, failed, active]

private theorem shifted_failure_budget (count : ℕ) :
    (∑ i : Fin count, ((16*((i : ℕ)+2)^2 : ℕ) : ℝ≥0∞)⁻¹) ≤ (1 : ℝ≥0∞)/8 := by
  have budget := total_failure_budget (count+1)
  have split : (∑ n ∈ Finset.range (count+1), ((16*(n+1)^2 : ℕ) : ℝ≥0∞)⁻¹) =
      ((16*(0+1)^2 : ℕ) : ℝ≥0∞)⁻¹ +
      ∑ i : Fin count, ((16*((i : ℕ)+2)^2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [Finset.sum_range_succ', add_comm]
    congr 1
    simpa only [Nat.add_assoc, Nat.reduceAdd] using
      (Fin.sum_univ_eq_sum_range (fun i => ((16*(i+2)^2 : ℕ) : ℝ≥0∞)⁻¹) count).symm
  rw [split] at budget
  exact (le_add_self).trans budget

/-- The expected number of missed active indices is at most one eighth,
uniformly in the number of source indices tested. -/
theorem missed_indices_integral (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ n, (G.layer n).Nonempty →
      G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) (count : ℕ) :
    (∫⁻ stream, ∑ i, failed G (((tests G.machine p count).run stream).1 i) ∂fairCoinMeasure) ≤
      (1 : ℝ≥0∞)/8 := by
  have means := FreshStreamSampler.sequence_lintegral_sum
    (List.ofFn (fun i : Fin count => test G.machine p (i+1))) (failed G)
  unfold tests
  rw [means]
  simp only [List.map_ofFn, List.sum_ofFn]
  exact (Finset.sum_le_sum (fun i _ => by
    simpa only [Function.comp_apply, Nat.add_assoc, Nat.reduceAdd] using test_failure_integral G p expected (i+1))).trans
      (shifted_failure_budget count)

def allCertified (G : UniformGenerators α) {count : ℕ} (result : Fin count → ℕ × Bool) : Prop :=
  ∀ i, (G.layer (result i).1).Nonempty → (result i).2 = true

omit [Fintype α] in
private theorem bad_indicator_le (G : UniformGenerators α) {count : ℕ}
    (result : Fin count → ℕ × Bool) :
    ({v : Fin count → ℕ × Bool | ¬allCertified G v}.indicator (fun _ => (1 : ℝ≥0∞))) result ≤
      ∑ i, failed G (result i) := by
  classical
  by_cases good : allCertified G result
  · simp [good]
  · have missing : ∃ i, (G.layer (result i).1).Nonempty ∧ (result i).2 = false := by
      simp only [allCertified, not_forall, Bool.not_eq_true] at good
      obtain ⟨i, active, flag⟩ := good
      exact ⟨i, active, flag⟩
    obtain ⟨i, active, flag⟩ := missing
    simp only [Set.indicator_of_mem (show result ∈ {v | ¬allCertified G v} from good)]
    calc
      1 = failed G (result i) := by simp [failed, active, flag]
      _ ≤ ∑ i, failed G (result i) := Finset.single_le_sum (f := fun i : Fin count => failed G (result i)) (fun _ _ => zero_le) (Finset.mem_univ i)

/-- With probability at least seven eighths, every active positive index up
to the target is recognised by its actual bounded native test. -/
theorem all_certified_lower_bound (G : UniformGenerators α) (p : PolynomialBound)
    (expected : ∀ n, (G.layer n).Nonempty →
      G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) (count : ℕ) :
    (1 : ℝ≥0∞)-(1 : ℝ≥0∞)/8 ≤ fairCoinMeasure {stream |
      allCertified G ((tests G.machine p count).run stream).1} := by
  classical
  have output : Measurable (fun stream => ((tests G.machine p count).run stream).1) :=
    measurable_fst.comp (tests G.machine p count).measurable
  have badMeasurable : MeasurableSet {stream |
      ¬allCertified G ((tests G.machine p count).run stream).1} :=
    output (show MeasurableSet {v : Fin (List.ofFn (fun i : Fin count => test G.machine p (i+1))).length → ℕ × Bool |
      ¬allCertified G v} from Set.to_countable _ |>.measurableSet)
  have bad : fairCoinMeasure {stream | ¬allCertified G ((tests G.machine p count).run stream).1} ≤
      (1 : ℝ≥0∞)/8 := by
    rw [← lintegral_indicator_one badMeasurable]
    refine (lintegral_mono (fun stream => ?_)).trans (missed_indices_integral G p expected count)
    exact bad_indicator_le G _
  have complement : {stream | allCertified G ((tests G.machine p count).run stream).1} =
      {stream | ¬allCertified G ((tests G.machine p count).run stream).1}ᶜ := by
    ext stream
    simp
  rw [complement, measure_compl badMeasurable (measure_ne_top _ _), measure_univ]
  exact tsub_le_tsub_left bad 1

end
end ComplexityOfGenerators.IndexwiseCertification
