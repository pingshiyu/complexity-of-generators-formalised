import ComplexityOfGenerators.Foundations.Probability
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable
import Mathlib.Analysis.SpecificLimits.Basic

/-! Fixed disjoint blocks of the actual fair-coin stream have the product law.
This supplies independence for bounded retry phases without assuming a retry
machine or an additional moment bound. -/

namespace ComplexityOfGenerators

open MeasureTheory Filter
open scoped ENNReal Topology

def fixedBlock (k : ℕ) (stream : BitStream) (phase : ℕ) : Fin k → Bool :=
  fun offset => stream (phase * k + offset.val)

noncomputable def fairBlockMeasure (k : ℕ) : Measure (Fin k → Bool) :=
  Measure.infinitePi (fun _ : Fin k => (PMF.uniformOfFintype Bool).toMeasure)

instance (k : ℕ) : IsProbabilityMeasure (fairBlockMeasure k) := by
  unfold fairBlockMeasure
  infer_instance

theorem measurable_fixedBlocks (k : ℕ) : Measurable (fixedBlock k) := by
  apply Measurable.of_eval
  intro phase
  apply Measurable.of_eval
  intro offset
  exact measurable_pi_apply _

/-- Reindexing the bit product by quotient and remainder gives an actual
product of independent finite-block laws. -/
theorem fairCoinMeasure_map_fixedBlocks (k : ℕ) (positive : 0 < k) :
    fairCoinMeasure.map (fixedBlock k) =
      Measure.infinitePi (fun _ : ℕ => fairBlockMeasure k) := by
  letI : NeZero k := ⟨positive.ne'⟩
  have reindexed : fairCoinMeasure.map (fun stream (position : ℕ × Fin k) =>
      stream (position.1 * k + position.2.val)) =
      Measure.infinitePi (fun _ : ℕ × Fin k => (PMF.uniformOfFintype Bool).toMeasure) := by
    have mapping : (fun stream (position : ℕ × Fin k) => stream (position.1 * k + position.2.val)) =
        ⇑(MeasurableEquiv.piCongrLeft (fun _ : ℕ × Fin k => Bool) (Nat.divModEquiv k)) := by
      funext stream position
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_eq_cast]
      simp [Nat.divModEquiv]
    rw [mapping]
    exact Measure.infinitePi_map_piCongrLeft
      (fun _ : ℕ × Fin k => (PMF.uniformOfFintype Bool).toMeasure) (Nat.divModEquiv k)
  have curried := Measure.infinitePi_map_curry
    (fun (_ : ℕ) (_ : Fin k) => (PMF.uniformOfFintype Bool).toMeasure)
  change fairCoinMeasure.map (fixedBlock k) =
    Measure.infinitePi (fun _ : ℕ => Measure.infinitePi (fun _ : Fin k => (PMF.uniformOfFintype Bool).toMeasure))
  rw [← curried, ← reindexed, Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- The finite-product formula for arbitrary measurable events in disjoint
blocks is the independence property needed by retry phases. -/
theorem fairCoinMeasure_fixedBlock_events (k : ℕ) (positive : 0 < k)
    (phases : Finset ℕ) (events : ℕ → Set (Fin k → Bool))
    (measurable : ∀ n, MeasurableSet (events n)) :
    fairCoinMeasure {stream | ∀ n ∈ phases, fixedBlock k stream n ∈ events n} =
      ∏ n ∈ phases, fairBlockMeasure k (events n) := by
  have preimage : {stream | ∀ n ∈ phases, fixedBlock k stream n ∈ events n} =
      (fixedBlock k) ⁻¹' Set.pi phases events := rfl
  rw [preimage, ← Measure.map_apply (measurable_fixedBlocks k)
    (MeasurableSet.pi phases.countable_toSet (fun n _ => measurable n)),
    fairCoinMeasure_map_fixedBlocks k positive,
    Measure.infinitePi_pi _ (fun n _ => measurable n)]

theorem fairCoinMeasure_fixedBlock_event (k : ℕ) (positive : 0 < k)
    (phase : ℕ) (event : Set (Fin k → Bool)) (measurable : MeasurableSet event) :
    fairCoinMeasure {stream | fixedBlock k stream phase ∈ event} = fairBlockMeasure k event := by
  simpa using fairCoinMeasure_fixedBlock_events k positive {phase} (fun _ => event) (fun _ => measurable)

def retryFailures (k : ℕ) (success : Set (Fin k → Bool)) (n : ℕ) : Set BitStream :=
  {stream | ∀ phase < n, fixedBlock k stream phase ∉ success}

theorem measurableSet_retryFailures (k : ℕ) (success : Set (Fin k → Bool))
    (measurable : MeasurableSet success) (n : ℕ) : MeasurableSet (retryFailures k success n) := by
  have description : retryFailures k success n =
      ⋂ phase : Fin n, {stream | fixedBlock k stream phase.val ∈ successᶜ} := by
    ext stream
    simp only [retryFailures, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_compl_iff]
    exact ⟨fun h phase => h phase.val phase.isLt, fun h phase bound => h ⟨phase, bound⟩⟩
  rw [description]
  exact MeasurableSet.iInter fun phase =>
    ((measurable_fixedBlocks k).eval (a := phase.val)) measurable.compl

theorem fairCoinMeasure_retryFailures (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success) (n : ℕ) :
    fairCoinMeasure (retryFailures k success n) = (1 - fairBlockMeasure k success) ^ n := by
  have formula := fairCoinMeasure_fixedBlock_events k positive (Finset.range n)
    (fun _ => successᶜ) (fun _ => measurable.compl)
  have same : {stream | ∀ phase ∈ Finset.range n, fixedBlock k stream phase ∈ successᶜ} =
      retryFailures k success n := by ext stream; simp [retryFailures]
  rw [same] at formula
  rw [measure_compl measurable (measure_ne_top _ _), measure_univ] at formula
  simpa using formula

theorem fairCoin_ae_fixedBlock_success (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) :
    ∀ᵐ stream ∂fairCoinMeasure, ∃ phase, fixedBlock k stream phase ∈ success := by
  rw [ae_iff]
  have bound (n : ℕ) :
      fairCoinMeasure {stream | ¬ ∃ phase, fixedBlock k stream phase ∈ success} ≤
        (1 - fairBlockMeasure k success) ^ n := by
    rw [← fairCoinMeasure_retryFailures k positive success measurable n]
    apply measure_mono
    intro stream absent phase _ member
    exact absent ⟨phase, member⟩
  have limit := ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one
    (ENNReal.sub_lt_self (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) one_ne_zero mass.ne')
  exact le_antisymm
    (le_of_tendsto_of_tendsto tendsto_const_nhds limit (Eventually.of_forall bound)) zero_le

def retryIndexValue (k : ℕ) (success : Set (Fin k → Bool)) (stream : BitStream) (n : ℕ) : Prop :=
  (fixedBlock k stream n ∈ success ∧ ∀ phase < n, fixedBlock k stream phase ∉ success) ∨
    (n = 0 ∧ ∀ phase, fixedBlock k stream phase ∉ success)

theorem retryIndexValue_exists (k : ℕ) (success : Set (Fin k → Bool)) (stream : BitStream) :
    ∃ n, retryIndexValue k success stream n := by
  classical
  by_cases found : ∃ phase, fixedBlock k stream phase ∈ success
  · exact ⟨Nat.find found, Or.inl ⟨Nat.find_spec found, fun phase earlier => Nat.find_min found earlier⟩⟩
  · exact ⟨0, Or.inr ⟨rfl, fun phase member => found ⟨phase, member⟩⟩⟩

/-- The first successful phase, with zero assigned on the null event where
all phases fail.  Counting attempted phases means adding one to this index. -/
noncomputable def firstSuccessIndex (k : ℕ) (success : Set (Fin k → Bool)) (stream : BitStream) : ℕ := by
  classical
  exact Nat.find (retryIndexValue_exists k success stream)

theorem firstSuccessIndex_spec (k : ℕ) (success : Set (Fin k → Bool)) (stream : BitStream) :
    retryIndexValue k success stream (firstSuccessIndex k success stream) := by
  classical
  exact Nat.find_spec (retryIndexValue_exists k success stream)

theorem measurable_firstSuccessIndex (k : ℕ) (success : Set (Fin k → Bool))
    (measurable : MeasurableSet success) : Measurable (firstSuccessIndex k success) := by
  classical
  apply measurable_find (retryIndexValue_exists k success)
  intro n
  have hit : MeasurableSet {stream | fixedBlock k stream n ∈ success} :=
    ((measurable_fixedBlocks k).eval (a := n)) measurable
  have never : MeasurableSet {stream | ∀ phase, fixedBlock k stream phase ∉ success} := by
    simp only [Set.ofPred_forall]
    exact MeasurableSet.iInter fun phase =>
      (((measurable_fixedBlocks k).eval (a := phase)) measurable).compl
  have fallback : MeasurableSet {stream | n = 0 ∧ ∀ phase, fixedBlock k stream phase ∉ success} := by
    by_cases zero : n = 0
    · simpa only [zero, true_and] using never
    · simp [zero]
  exact (hit.inter (measurableSet_retryFailures k success measurable n)).union fallback

theorem firstSuccessIndex_ae_success (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) :
    ∀ᵐ stream ∂fairCoinMeasure,
      fixedBlock k stream (firstSuccessIndex k success stream) ∈ success := by
  filter_upwards [fairCoin_ae_fixedBlock_success k positive success measurable mass] with stream found
  rcases firstSuccessIndex_spec k success stream with ⟨hit, _⟩ | ⟨_, never⟩
  · exact hit
  · obtain ⟨phase, hit⟩ := found
    exact False.elim (never phase hit)

theorem firstSuccessIndex_tail_subset (k : ℕ) (success : Set (Fin k → Bool)) (n : ℕ) :
    {stream | n ≤ firstSuccessIndex k success stream} ⊆ retryFailures k success n := by
  intro stream later phase earlier
  rcases firstSuccessIndex_spec k success stream with ⟨_, minimal⟩ | ⟨_, never⟩
  · exact minimal phase (lt_of_lt_of_le earlier later)
  · exact never phase

theorem fairCoinMeasure_firstSuccessIndex_tail_le (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success) (n : ℕ) :
    fairCoinMeasure {stream | n ≤ firstSuccessIndex k success stream} ≤
      (1 - fairBlockMeasure k success) ^ n := by
  rw [← fairCoinMeasure_retryFailures k positive success measurable n]
  exact measure_mono (firstSuccessIndex_tail_subset k success n)

private def triangularPairEquiv : (Σ n : ℕ, Fin (n + 1)) ≃ ℕ × ℕ where
  toFun position := (position.2.val, position.1 - position.2.val)
  invFun pair := ⟨pair.1 + pair.2, ⟨pair.1, by omega⟩⟩
  left_inv := by
    rintro ⟨n, position⟩
    have equal : position.val + (n - position.val) = n := by have := position.isLt; omega
    apply Sigma.ext equal
    exact (Fin.heq_ext_iff (congrArg (fun n => n + 1) equal)).mpr rfl
  right_inv := by
    rintro ⟨a, b⟩
    apply Prod.ext <;> simp

/-- A nonnegative Cauchy-product calculation, requiring no additional
summability hypothesis or real-valued geometric-distribution import. -/
theorem tsum_succ_mul_geometric (r : ℝ≥0∞) :
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * r ^ n) = ((1 - r)⁻¹) ^ 2 := by
  have total (position : Σ n : ℕ, Fin (n + 1)) :
      (triangularPairEquiv position).1 + (triangularPairEquiv position).2 = position.1 := by
    have := position.2.isLt
    simp only [triangularPairEquiv, Equiv.coe_fn_mk]
    omega
  calc
    (∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * r ^ n) =
        ∑' n : ℕ, ∑' _position : Fin (n + 1), r ^ n := by
          apply tsum_congr
          intro n
          simp [tsum_fintype]
    _ = ∑' position : Σ n : ℕ, Fin (n + 1), r ^ position.1 := (ENNReal.tsum_sigma _).symm
    _ = ∑' pair : ℕ × ℕ, r ^ (pair.1 + pair.2) := by
      have reindex := triangularPairEquiv.tsum_eq (fun pair : ℕ × ℕ => r ^ (pair.1 + pair.2))
      simpa only [total] using reindex
    _ = ∑' a : ℕ, ∑' b : ℕ, r ^ (a + b) := ENNReal.tsum_prod (f := fun a b : ℕ => r ^ (a + b))
    _ = (∑' a : ℕ, r ^ a) * (∑' b : ℕ, r ^ b) := by
      simp only [pow_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]
    _ = _ := by rw [ENNReal.tsum_geometric, pow_two]

/-- A geometric upper bound on the tails of a natural random variable gives
a quadratic moment bound.  This is an integral statement, not a moment premise
attached to a machine interface. -/
theorem lintegral_succ_sq_le_of_geometric_tails {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) (index : Ω → ℕ) (measurable : Measurable index) (r : ℝ≥0∞)
    (tails : ∀ n : ℕ, μ {x | n ≤ index x} ≤ r ^ n) :
    (∫⁻ x, (((index x + 1 : ℕ) : ℝ≥0∞) ^ 2) ∂μ) ≤ 2 * ((1 - r)⁻¹) ^ 2 := by
  classical
  let term (n : ℕ) : Ω → ℝ≥0∞ := {x | n ≤ index x}.indicator (fun _ => ((n + 1 : ℕ) : ℝ≥0∞))
  have measurableSet (n : ℕ) : MeasurableSet {x | n ≤ index x} := measurableSet_le measurable_const measurable
  have measurableTerm (n : ℕ) : Measurable (term n) := measurable_const.indicator (measurableSet n)
  have finiteCount (n : ℕ) : (n + 1) ^ 2 ≤ 2 * ∑ j ∈ Finset.range (n + 1), (j + 1) := by
    induction n with
    | zero => norm_num
    | succ n ih =>
        rw [Finset.sum_range_succ]
        nlinarith
  have pointwise (x : Ω) : ((index x + 1 : ℕ) : ℝ≥0∞) ^ 2 ≤ 2 * ∑' n : ℕ, term n x := by
    calc
      ((index x + 1 : ℕ) : ℝ≥0∞) ^ 2 ≤
          2 * ∑ n ∈ Finset.range (index x + 1), ((n + 1 : ℕ) : ℝ≥0∞) := by
            exact_mod_cast finiteCount (index x)
      _ = 2 * ∑ n ∈ Finset.range (index x + 1), term n x := by
        congr 1
        apply Finset.sum_congr rfl
        intro n member
        have bound : n ≤ index x := by have := Finset.mem_range.mp member; omega
        simp [term, bound]
      _ ≤ 2 * ∑' n : ℕ, term n x := by
        gcongr
        exact ENNReal.sum_le_tsum _
  calc
    (∫⁻ x, (((index x + 1 : ℕ) : ℝ≥0∞) ^ 2) ∂μ) ≤
        ∫⁻ x, 2 * ∑' n : ℕ, term n x ∂μ := lintegral_mono pointwise
    _ = 2 * ∑' n : ℕ, ∫⁻ x, term n x ∂μ := by
      rw [lintegral_const_mul 2 (Measurable.ennreal_tsum measurableTerm),
        lintegral_tsum (fun n => (measurableTerm n).aemeasurable)]
    _ = 2 * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * μ {x | n ≤ index x} := by
      congr 1
      apply tsum_congr
      intro n
      exact lintegral_indicator_const (measurableSet n) _
    _ ≤ 2 * ∑' n : ℕ, ((n + 1 : ℕ) : ℝ≥0∞) * r ^ n := by
      gcongr with n
      exact tails n
    _ = 2 * ((1 - r)⁻¹) ^ 2 := by rw [tsum_succ_mul_geometric]

/-- The attempted-phase count has polynomially bounded second moment when
one bounded phase succeeds with inverse-polynomial probability. -/
theorem firstSuccessIndex_secondMoment_le (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success) :
    (∫⁻ stream, (((firstSuccessIndex k success stream + 1 : ℕ) : ℝ≥0∞) ^ 2) ∂fairCoinMeasure) ≤
      2 / (fairBlockMeasure k success) ^ 2 := by
  have bound := lintegral_succ_sq_le_of_geometric_tails fairCoinMeasure
    (firstSuccessIndex k success) (measurable_firstSuccessIndex k success measurable)
    (1 - fairBlockMeasure k success)
    (fairCoinMeasure_firstSuccessIndex_tail_le k positive success measurable)
  have massLe : fairBlockMeasure k success ≤ 1 := prob_le_one
  rw [ENNReal.sub_sub_cancel (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) massLe] at bound
  simpa only [div_eq_mul_inv, ENNReal.inv_pow] using bound

theorem fixedBlock_retries_ae_and_secondMoment (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) :
    (∀ᵐ stream ∂fairCoinMeasure,
      fixedBlock k stream (firstSuccessIndex k success stream) ∈ success) ∧
    (∫⁻ stream, (((firstSuccessIndex k success stream + 1 : ℕ) : ℝ≥0∞) ^ 2) ∂fairCoinMeasure) ≤
      2 / (fairBlockMeasure k success) ^ 2 :=
  ⟨firstSuccessIndex_ae_success k positive success measurable mass,
    firstSuccessIndex_secondMoment_le k positive success measurable⟩

/-- A quadratic cost bound can be integrated using the proved retry moment;
the caller supplies its actual cost inequality rather than a moment premise. -/
theorem fixedBlock_retry_expected_cost_le (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (cost : BitStream → ℝ≥0∞) (constant : ℝ≥0∞)
    (bounded : ∀ᵐ stream ∂fairCoinMeasure, cost stream ≤
      constant * (((firstSuccessIndex k success stream + 1 : ℕ) : ℝ≥0∞) ^ 2)) :
    (∫⁻ stream, cost stream ∂fairCoinMeasure) ≤
      constant * (2 / (fairBlockMeasure k success) ^ 2) := by
  have measurableMoment : Measurable (fun stream =>
      (((firstSuccessIndex k success stream + 1 : ℕ) : ℝ≥0∞) ^ 2)) :=
    (measurable_of_countable (fun n : ℕ => (((n + 1 : ℕ) : ℝ≥0∞) ^ 2))).comp
      (measurable_firstSuccessIndex k success measurable)
  calc
    (∫⁻ stream, cost stream ∂fairCoinMeasure) ≤
        ∫⁻ stream, constant * (((firstSuccessIndex k success stream + 1 : ℕ) : ℝ≥0∞) ^ 2)
          ∂fairCoinMeasure := lintegral_mono_ae bounded
    _ = constant * ∫⁻ stream, (((firstSuccessIndex k success stream + 1 : ℕ) : ℝ≥0∞) ^ 2)
        ∂fairCoinMeasure := lintegral_const_mul constant measurableMoment
    _ ≤ _ := by
      gcongr
      exact firstSuccessIndex_secondMoment_le k positive success measurable

end ComplexityOfGenerators
