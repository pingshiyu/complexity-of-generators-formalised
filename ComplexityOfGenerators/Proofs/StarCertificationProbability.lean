import ComplexityOfGenerators.Simulation.StarCertification.Support
import ComplexityOfGenerators.Foundations.CertificationErrors
import ComplexityOfGenerators.Foundations.BalancedPairProbability

/-! The cache built by the concrete native scan recognises all active source
indices with constant probability. Each marginal is an actual disjoint stream
block; a summable union bound avoids any oracle or independence assumption. -/
namespace ComplexityOfGenerators.Simulation.StarCertification
open MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α]

def allActiveCertified (G : UniformGenerators α) (p : PolynomialBound) (target : ℕ) (bits : BitString) : Prop :=
  ∀ i : Fin target, (G.layer (i+1)).Nonempty →
    (((walk G.machine p 0 target bits).1)[i.val]?).getD false = true

private theorem segment_fits (p : PolynomialBound) (target k : ℕ) (inside : k < target) :
    used p 0 k+IndexwiseCertification.seed p (k+1) ≤ width p target := by
  have before := used_bound p 0 k
  simp only [Nat.zero_add] at before
  have earlier := (IndexwiseCertification.seed p).monotone (show k ≤ target by omega)
  have current := (IndexwiseCertification.seed p).monotone (show k+1 ≤ target by omega)
  have bound := width_lower p target
  have previous : used p 0 k ≤ k*IndexwiseCertification.seed p target :=
    before.trans (Nat.mul_le_mul_left k earlier)
  have number := Nat.mul_le_mul_right (IndexwiseCertification.seed p target) (show k+1 ≤ target by omega)
  nlinarith

private theorem native_flag_stream (M : Machine Unit Bool α) (p : PolynomialBound) (target k : ℕ)
    (inside : k < target) (stream : BitStream) :
    (((walk M p 0 target (streamPrefix stream (width p target))).1)[k]?).getD false =
      IndexwiseCertification.accepts M p (k+1)
        (fun i => stream (used p 0 k+i.val)) := by
  rw [walk_lookup M p 0 target (streamPrefix stream (width p target)) k inside]
  simp only [Option.getD_some,Nat.zero_add,testFlag,IndexwiseCertification.accepts]
  rw [BalancedPairPhase.streamPrefix_drop_take stream (width p target) (used p 0 k)
    (IndexwiseCertification.seed p (k+1)) (segment_fits p target k inside)]

private theorem shifted_test_failure (M : Machine Unit Bool α) (p : PolynomialBound) (j offset : ℕ)
    (expected : M.expectedRuntime (generatorData j) ≤ (p j : ℝ≥0∞)) :
    fairCoinMeasure {stream | IndexwiseCertification.accepts M p j
      (fun i => stream (offset+i.val)) = false} ≤ ((16*(j+1)^2 : ℕ) : ℝ≥0∞)⁻¹ := by
  let event : Set BitStream := {stream | IndexwiseCertification.accepts M p j
    (splitStream (IndexwiseCertification.seed p j) stream).1 = false}
  have finiteMeasurable : MeasurableSet {bits | IndexwiseCertification.accepts M p j bits = false} :=
    Set.to_countable _ |>.measurableSet
  have eventMeasurable : MeasurableSet event :=
    (measurable_fst.comp (measurable_splitStream (IndexwiseCertification.seed p j))) finiteMeasurable
  have shifted := fairCoinMeasure_prefix_tail offset Set.univ event MeasurableSet.univ eventMeasurable
  simp only [Set.mem_univ,true_and,measure_univ,one_mul] at shifted
  have finite := fairCoinMeasure_prefix_tail (IndexwiseCertification.seed p j)
    {bits | IndexwiseCertification.accepts M p j bits = false} Set.univ finiteMeasurable MeasurableSet.univ
  simp only [Set.mem_univ,and_true,measure_univ,mul_one] at finite
  have same : {stream | IndexwiseCertification.accepts M p j
      (fun i => stream (offset+i.val)) = false} = {stream | (splitStream offset stream).2 ∈ event} := rfl
  rw [same,shifted]
  exact finite.le.trans (IndexwiseCertification.failure_upper_bound M p j expected)

private theorem native_flag_failure (G : UniformGenerators α) (p : PolynomialBound) (target : ℕ)
    (expected : ∀ n, (G.layer n).Nonempty →
      G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) (i : Fin target) :
    fairBlockMeasure (width p target) {bits | (G.layer (i+1)).Nonempty ∧
      (((walk G.machine p 0 target (List.ofFn bits)).1)[i.val]?).getD false = false} ≤
      ((16*((i : ℕ)+2)^2 : ℕ) : ℝ≥0∞)⁻¹ := by
  classical
  by_cases active : (G.layer (i+1)).Nonempty
  · have measurable : MeasurableSet {bits : Fin (width p target) → Bool |
        (((walk G.machine p 0 target (List.ofFn bits)).1)[i.val]?).getD false = false} :=
      Set.to_countable _ |>.measurableSet
    have law := fairCoinMeasure_prefix_tail (width p target)
      {bits | (((walk G.machine p 0 target (List.ofFn bits)).1)[i.val]?).getD false = false}
      Set.univ measurable MeasurableSet.univ
    simp only [Set.mem_univ,and_true,measure_univ,mul_one,Set.mem_ofPred_eq] at law
    have streamWord (stream : BitStream) :
        List.ofFn (splitStream (width p target) stream).1 = streamPrefix stream (width p target) := rfl
    simp_rw [streamWord,native_flag_stream G.machine p target i.val i.isLt] at law
    simp only [active,true_and]
    rw [← law]
    simpa only [Nat.add_assoc,Nat.reduceAdd] using
      shifted_test_failure G.machine p (i+1) (used p 0 i.val) (expected (i+1) active)
  · simp [active]

private theorem positive_error_budget (target : ℕ) :
    (∑ i : Fin target, ((16*((i : ℕ)+2)^2 : ℕ) : ℝ≥0∞)⁻¹) ≤ (1 : ℝ≥0∞)/8 := by
  have total := IndexwiseCertification.total_failure_budget (target+1)
  rw [Finset.sum_range_succ',add_comm] at total
  have same := Fin.sum_univ_eq_sum_range (fun i => ((16*(i+2)^2 : ℕ) : ℝ≥0∞)⁻¹) target
  have bound : (∑ i : Fin target, ((16*((i : ℕ)+2)^2 : ℕ) : ℝ≥0∞)⁻¹) ≤
      ((16*(0+1)^2 : ℕ) : ℝ≥0∞)⁻¹+
        ∑ k ∈ Finset.range target, ((16*(k+1+1)^2 : ℕ) : ℝ≥0∞)⁻¹ := by
    rw [same]
    simp only [Nat.add_assoc,Nat.reduceAdd]
    exact le_add_self
  exact bound.trans total

/-- Uniform constant success probability for the actual finite test cache,
using only the original source's first expected-runtime bound. -/
theorem allActiveCertified_mass (G : UniformGenerators α) (p : PolynomialBound) (target : ℕ)
    (expected : ∀ n, (G.layer n).Nonempty →
      G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) :
    (1 : ℝ≥0∞)-(1 : ℝ≥0∞)/8 ≤ fairBlockMeasure (width p target)
      {bits | allActiveCertified G p target (List.ofFn bits)} := by
  classical
  let bad : Fin target → Set (Fin (width p target) → Bool) := fun i =>
    {bits | (G.layer (i+1)).Nonempty ∧
      (((walk G.machine p 0 target (List.ofFn bits)).1)[i.val]?).getD false = false}
  have budget : fairBlockMeasure (width p target) (⋃ i, bad i) ≤ (1 : ℝ≥0∞)/8 := by
    calc
      _ ≤ ∑ i, fairBlockMeasure (width p target) (bad i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ i : Fin target, ((16*((i : ℕ)+2)^2 : ℕ) : ℝ≥0∞)⁻¹ :=
        Finset.sum_le_sum (fun i _ => native_flag_failure G p target expected i)
      _ ≤ _ := positive_error_budget target
  have complement : {bits : Fin (width p target) → Bool | allActiveCertified G p target (List.ofFn bits)} =
      (⋃ i, bad i)ᶜ := by
    ext bits
    simp [allActiveCertified,bad]
  rw [complement,measure_compl (Set.to_countable _ |>.measurableSet) (measure_ne_top _ _),measure_univ]
  exact tsub_le_tsub_left budget 1

end
end ComplexityOfGenerators.Simulation.StarCertification
