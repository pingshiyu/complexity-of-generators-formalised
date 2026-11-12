import ComplexityOfGenerators.Foundations.FixedBlockRetries

/-! The selected successful block has the finite phase law conditioned on
success. This supplies support and mean transfer for native retry controllers. -/
namespace ComplexityOfGenerators
open MeasureTheory
open scoped ENNReal


def retryHit (k : ℕ) (success target : Set (Fin k → Bool)) (n : ℕ) : Set BitStream :=
  retryFailures k success n ∩ {stream | fixedBlock k stream n ∈ target}

theorem measurableSet_retryHit (k : ℕ) (success target : Set (Fin k → Bool))
    (successMeasurable : MeasurableSet success) (targetMeasurable : MeasurableSet target) (n : ℕ) :
    MeasurableSet (retryHit k success target n) :=
  (measurableSet_retryFailures k success successMeasurable n).inter
    (((measurable_fixedBlocks k).eval (a := n)) targetMeasurable)

theorem fairCoinMeasure_retryHit (k : ℕ) (positive : 0 < k)
    (success target : Set (Fin k → Bool)) (successMeasurable : MeasurableSet success)
    (targetMeasurable : MeasurableSet target) (n : ℕ) :
    fairCoinMeasure (retryHit k success target n) =
      (1 - fairBlockMeasure k success)^n * fairBlockMeasure k target := by
  let events : ℕ → Set (Fin k → Bool) := fun j => if j = n then target else successᶜ
  have same : retryHit k success target n =
      {stream | ∀ j ∈ Finset.range (n+1), fixedBlock k stream j ∈ events j} := by
    ext stream
    constructor
    · rintro ⟨failed, hit⟩ j member
      by_cases equal : j = n
      · simpa [events, equal] using hit
      · have earlier : j < n := by have := Finset.mem_range.mp member; omega
        simpa [events, equal] using failed j earlier
    · intro all
      refine ⟨?_, ?_⟩
      · intro j earlier
        have := all j (Finset.mem_range.mpr (by omega))
        simpa [events, show j ≠ n by omega] using this
      · simpa [events] using all n (Finset.mem_range.mpr (by omega))
  rw [same, fairCoinMeasure_fixedBlock_events k positive _ events
    (fun j => by unfold events; split <;> simp_all)]
  rw [Finset.prod_range_succ]
  have previous : (∏ j ∈ Finset.range n, fairBlockMeasure k (events j)) =
      (1 - fairBlockMeasure k success)^n := by
    calc
      _ = ∏ _j ∈ Finset.range n, fairBlockMeasure k successᶜ := by
        apply Finset.prod_congr rfl
        intro j member
        have earlier := Finset.mem_range.mp member
        simp [events, show j ≠ n by omega]
      _ = _ := by
        rw [measure_compl successMeasurable (measure_ne_top _ _), measure_univ]
        simp
  rw [previous]
  simp [events]

theorem retryHits_pairwiseDisjoint (k : ℕ) (success target : Set (Fin k → Bool))
    (subset : target ⊆ success) : Pairwise (fun n m => Disjoint (retryHit k success target n) (retryHit k success target m)) := by
  intro n m different
  apply Set.disjoint_left.mpr
  intro stream left right
  rcases lt_or_gt_of_ne different with earlier | earlier
  · exact right.1 n earlier (subset left.2)
  · exact left.1 m earlier (subset right.2)

theorem firstSuccessIndex_eq_of_retryHit (k : ℕ) (success target : Set (Fin k → Bool))
    (subset : target ⊆ success) (stream : BitStream) (n : ℕ)
    (hit : stream ∈ retryHit k success target n) : firstSuccessIndex k success stream = n := by
  rcases firstSuccessIndex_spec k success stream with ⟨found, minimal⟩ | ⟨_, never⟩
  · by_contra different
    rcases lt_or_gt_of_ne different with earlier | earlier
    · exact hit.1 _ earlier found
    · exact minimal n earlier (subset hit.2)
  · exact False.elim (never n (subset hit.2))

theorem selectedBlock_event_eq_iUnion (k : ℕ) (success target : Set (Fin k → Bool))
    (subset : target ⊆ success) :
    {stream | fixedBlock k stream (firstSuccessIndex k success stream) ∈ target} =
      ⋃ n, retryHit k success target n := by
  ext stream
  constructor
  · intro member
    apply Set.mem_iUnion.mpr
    refine ⟨firstSuccessIndex k success stream, ?_, member⟩
    intro phase earlier
    rcases firstSuccessIndex_spec k success stream with ⟨_, minimal⟩ | ⟨_, never⟩
    · exact minimal phase earlier
    · exact never phase
  · intro member
    obtain ⟨n, hit⟩ := Set.mem_iUnion.mp member
    change fixedBlock k stream (firstSuccessIndex k success stream) ∈ target
    rw [firstSuccessIndex_eq_of_retryHit k success target subset stream n hit]
    exact hit.2

/-- First-success selection is exactly conditioning one independent block on
success, rather than introducing a distributional premise for the machine. -/
theorem fairCoinMeasure_selectedBlock_event (k : ℕ) (positive : 0 < k)
    (success target : Set (Fin k → Bool)) (successMeasurable : MeasurableSet success)
    (targetMeasurable : MeasurableSet target) (subset : target ⊆ success) :
    fairCoinMeasure {stream | fixedBlock k stream (firstSuccessIndex k success stream) ∈ target} =
      fairBlockMeasure k target / fairBlockMeasure k success := by
  rw [selectedBlock_event_eq_iUnion k success target subset,
    measure_iUnion (retryHits_pairwiseDisjoint k success target subset)
      (measurableSet_retryHit k success target successMeasurable targetMeasurable)]
  simp only [fairCoinMeasure_retryHit k positive success target successMeasurable targetMeasurable]
  rw [ENNReal.tsum_mul_right, ENNReal.tsum_geometric]
  have bounded : fairBlockMeasure k success ≤ 1 := prob_le_one
  rw [ENNReal.sub_sub_cancel (by norm_num : (1 : ℝ≥0∞) ≠ ⊤) bounded]
  simp only [div_eq_mul_inv, mul_comm]

noncomputable def selectedBlock (k : ℕ) (success : Set (Fin k → Bool)) (stream : BitStream) : Fin k → Bool :=
  fixedBlock k stream (firstSuccessIndex k success stream)

theorem measurable_selectedBlock (k : ℕ) (success : Set (Fin k → Bool))
    (measurable : MeasurableSet success) : Measurable (selectedBlock k success) := by
  intro target targetMeasurable
  have description : (selectedBlock k success) ⁻¹' target =
      ⋃ n : ℕ, {stream | firstSuccessIndex k success stream = n} ∩
        {stream | fixedBlock k stream n ∈ target} := by
    ext stream
    simp only [Set.mem_preimage, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_ofPred_eq, selectedBlock]
    exact ⟨fun hit => ⟨_, rfl, hit⟩, fun ⟨n, equal, hit⟩ => by simpa only [equal] using hit⟩
  rw [description]
  apply MeasurableSet.iUnion
  intro n
  exact (measurableSet_eq_fun (measurable_firstSuccessIndex k success measurable) measurable_const).inter
    (((measurable_fixedBlocks k).eval (a := n)) targetMeasurable)

/-- The selected finite block has the success-conditioned phase distribution. -/
theorem fairCoinMeasure_map_selectedBlock (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) :
    fairCoinMeasure.map (selectedBlock k success) =
      (fairBlockMeasure k success)⁻¹ • (fairBlockMeasure k).restrict success := by
  apply Measure.ext
  intro target targetMeasurable
  rw [Measure.map_apply (measurable_selectedBlock k success measurable) targetMeasurable]
  have same : (selectedBlock k success) ⁻¹' target =ᵐ[fairCoinMeasure]
      {stream | selectedBlock k success stream ∈ target ∩ success} := by
    filter_upwards [firstSuccessIndex_ae_success k positive success measurable mass] with stream hit
    simp only [Set.mem_preimage, Set.mem_ofPred_eq, Set.mem_inter_iff, selectedBlock] at *
    exact propext ⟨fun member => ⟨member, hit⟩, And.left⟩
  rw [measure_congr same]
  change fairCoinMeasure {stream | fixedBlock k stream (firstSuccessIndex k success stream) ∈ target ∩ success} = _
  rw [fairCoinMeasure_selectedBlock_event k positive success (target ∩ success) measurable
    (targetMeasurable.inter measurable) Set.inter_subset_right]
  simp only [Measure.smul_apply, Measure.restrict_apply targetMeasurable, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Retrying transfers the conditional first moment of a bounded phase exactly. -/
theorem lintegral_selectedBlock (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) (value : (Fin k → Bool) → ℝ≥0∞)
    (valueMeasurable : Measurable value) :
    (∫⁻ stream, value (selectedBlock k success stream) ∂fairCoinMeasure) =
      (fairBlockMeasure k success)⁻¹ * ∫⁻ block in success, value block ∂fairBlockMeasure k := by
  rw [← lintegral_map valueMeasurable (measurable_selectedBlock k success measurable),
    fairCoinMeasure_map_selectedBlock k positive success measurable mass,
    lintegral_smul_measure, smul_eq_mul]

/-- A phase whose length contribution is zero on failure and has mean
`target * successMass` yields exact target mean after retrying. -/
theorem lintegral_selectedBlock_eq_of_phase_mean (k : ℕ) (positive : 0 < k)
    (success : Set (Fin k → Bool)) (measurable : MeasurableSet success)
    (mass : 0 < fairBlockMeasure k success) (value : (Fin k → Bool) → ℝ≥0∞)
    (valueMeasurable : Measurable value) (zero : ∀ block ∉ success, value block = 0)
    (target : ℝ≥0∞) (mean : (∫⁻ block, value block ∂fairBlockMeasure k) = target * fairBlockMeasure k success) :
    (∫⁻ stream, value (selectedBlock k success stream) ∂fairCoinMeasure) = target := by
  have restricted : (∫⁻ block in success, value block ∂fairBlockMeasure k) =
      ∫⁻ block, value block ∂fairBlockMeasure k := by
    rw [← lintegral_indicator measurable]
    congr 1
    funext block
    by_cases member : block ∈ success
    · simp [member]
    · simp [member, zero block member]
  rw [lintegral_selectedBlock k positive success measurable mass value valueMeasurable, restricted, mean]
  rw [mul_comm target, ← mul_assoc, ENNReal.inv_mul_cancel mass.ne' (measure_ne_top _ _), one_mul]

end ComplexityOfGenerators
