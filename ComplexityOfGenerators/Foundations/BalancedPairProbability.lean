import ComplexityOfGenerators.Foundations.BalancedLengthBounds
import ComplexityOfGenerators.Foundations.BalancedPairPhase
import ComplexityOfGenerators.Foundations.RationalSelectionProbability

/-! Probability and mean of the executable finite balanced-pair phase. -/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

namespace BalancedPairPhase

variable {α : Type}

def optionLength (answer : Option (List α)) : ℕ := answer.elim 0 List.length

def tripleValue (M : Machine Unit Bool α) (i time sourceWidth selectorWidth : ℕ)
    (bits : (Fin sourceWidth → Bool) × (Fin sourceWidth → Bool) × (Fin sourceWidth → Bool)) : Option (List α) :=
  balance i (cappedCall M i time (List.ofFn bits.1))
    (cappedCall M i time (List.ofFn bits.2.1)) ((List.ofFn bits.2.2).take selectorWidth)

theorem streamPrefix_drop_take (stream : BitStream) (total offset count : ℕ)
    (enough : offset + count ≤ total) :
    ((streamPrefix stream total).drop offset).take count =
      List.ofFn (fun index : Fin count => stream (offset + index.val)) := by
  apply List.ext_getElem
  · simp only [List.length_take, List.length_drop, streamPrefix_length, List.length_ofFn]
    omega
  · intro index left right
    simp [streamPrefix, List.getElem_take, List.getElem_drop, List.getElem_ofFn]

theorem ofFn_fixedBlock_take (width count phase : ℕ) (enough : count ≤ width) (stream : BitStream) :
    (List.ofFn (fixedBlock width stream phase)).take count =
      List.ofFn (fun index : Fin count => stream (phase * width + index.val)) := by
  rw [← ofFn_takeBitVector width count enough]
  rfl

theorem value_streamPrefix_eq_triple (M : Machine Unit Bool α)
    (i time sourceWidth selectorWidth totalWidth : ℕ)
    (selectorFits : selectorWidth ≤ sourceWidth)
    (totalFits : 2 * sourceWidth + selectorWidth ≤ totalWidth) (stream : BitStream) :
    value M i time sourceWidth selectorWidth (streamPrefix stream totalWidth) =
      tripleValue M i time sourceWidth selectorWidth (fixedBlockTriple sourceWidth stream) := by
  unfold value tripleValue fixedBlockTriple
  have first : (streamPrefix stream totalWidth).take sourceWidth =
      List.ofFn (fixedBlock sourceWidth stream 0) := by
    change _ = List.ofFn (fun index : Fin sourceWidth => stream (0 * sourceWidth + index.val))
    simpa using streamPrefix_drop_take stream totalWidth 0 sourceWidth (by omega)
  have second : ((streamPrefix stream totalWidth).drop sourceWidth).take sourceWidth =
      List.ofFn (fixedBlock sourceWidth stream 1) := by
    change _ = List.ofFn (fun index : Fin sourceWidth => stream (1 * sourceWidth + index.val))
    simpa using streamPrefix_drop_take stream totalWidth sourceWidth sourceWidth (by omega)
  have selector : ((streamPrefix stream totalWidth).drop (2 * sourceWidth)).take selectorWidth =
      (List.ofFn (fixedBlock sourceWidth stream 2)).take selectorWidth := by
    rw [streamPrefix_drop_take stream totalWidth (2 * sourceWidth) selectorWidth totalFits,
      ofFn_fixedBlock_take sourceWidth selectorWidth 2 selectorFits]
  simp only [first, second, selector]

theorem choose_take_eq (denominator numerator count : ℕ) (bits : BitString)
    (enough : Nat.clog 2 denominator ≤ count) :
    Simulation.WordStack.RationalSelection.choose denominator numerator (bits.take count) =
      Simulation.WordStack.RationalSelection.choose denominator numerator bits := by
  simp only [Simulation.WordStack.RationalSelection.choose, List.take_take, Nat.min_eq_left enough]

/-- Padded selector bits have no effect once they include the bounded draw. -/
theorem balance_take_eq (target bound : ℕ) (first second : Option (List α))
    (selector : BitString)
    (firstBound : ∀ word, first = some word → word.length ≤ bound)
    (secondBound : ∀ word, second = some word → word.length ≤ bound) :
    balance target first second (selector.take bound) = balance target first second selector := by
  cases first with
  | none => rfl
  | some left =>
      cases second with
      | none => rfl
      | some right =>
          have leftBound := firstBound left rfl
          have rightBound := secondBound right rfl
          have below : Nat.clog 2 (right.length - left.length) ≤ bound :=
            (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
          have above : Nat.clog 2 (left.length - right.length) ≤ bound :=
            (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
          simp only [balance]
          split_ifs <;> simp only [choose_take_eq _ _ _ _ below, choose_take_eq _ _ _ _ above]


theorem optionLength_map_choice (lower upper : List α) (choice : Option Bool) :
    optionLength (choice.map (fun below => if below then lower else upper)) =
      chosenNat lower.length upper.length choice := by
  cases choice with
  | none => rfl
  | some flag => cases flag <;> rfl

/-- Each fixed input pair either rejects, is already on the desired length,
or has the exact accepted first moment of the rational selector. -/
theorem lintegral_balance_length (width target bound : ℕ) (first second : Option (List α))
    (enough : bound ≤ width)
    (firstBound : ∀ word, first = some word → word.length ≤ bound)
    (secondBound : ∀ word, second = some word → word.length ≤ bound) :
    (∫⁻ bits, (optionLength (balance target first second ((List.ofFn bits).take bound)) : ℝ≥0∞)
      ∂fairBlockMeasure width) =
      (target : ℝ≥0∞) * fairBlockMeasure width
        {bits | (balance target first second ((List.ofFn bits).take bound)).isSome} := by
  classical
  simp_rw [balance_take_eq target bound first second _ firstBound secondBound]
  cases first with
  | none => simp [balance, optionLength]
  | some left =>
      cases second with
      | none => simp [balance, optionLength]
      | some right =>
          have leftBound := firstBound left rfl
          have rightBound := secondBound right rfl
          have lowWidth : Nat.clog 2 (right.length - left.length) ≤ width :=
            (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
          have highWidth : Nat.clog 2 (left.length - right.length) ≤ width :=
            (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
          by_cases equal : left.length = target ∧ right.length = target
          · simp [balance, equal, optionLength]
          by_cases below : left.length < target ∧ target < right.length
          · simpa only [balance, ite_eq_right equal, ite_eq_left below, optionLength_map_choice, Option.isSome_map] using
              lintegral_choose_bracketing width left.length target right.length below.1 below.2 lowWidth
          by_cases above : right.length < target ∧ target < left.length
          · simpa only [balance, ite_eq_right equal, ite_eq_right below, ite_eq_left above, optionLength_map_choice, Option.isSome_map] using
              lintegral_choose_bracketing width right.length target left.length above.1 above.2 highWidth
          · simp [balance, equal, below, above, optionLength]

/-- An ordered strict bracketing input pair succeeds with probability at least one half. -/
theorem balance_strict_success_ge_half (width target bound : ℕ) (lower upper : List α)
    (below : lower.length < target) (above : target < upper.length)
    (upperBound : upper.length ≤ bound) (enough : bound ≤ width) :
    (2 : ℝ≥0∞)⁻¹ ≤ fairBlockMeasure width
      {bits | (balance target (some lower) (some upper) ((List.ofFn bits).take bound)).isSome} := by
  have lowerBound : lower.length ≤ bound := by omega
  simp_rw [balance_take_eq target bound (some lower) (some upper) _
    (by intro word same; cases same; exact lowerBound)
    (by intro word same; cases same; exact upperBound)]
  have equal : ¬ (lower.length = target ∧ upper.length = target) := by omega
  have pair : lower.length < target ∧ target < upper.length := ⟨below, above⟩
  simp only [balance, ite_eq_right equal, ite_eq_left pair, Option.isSome_map]
  apply fairBlockMeasure_choose_success_ge_half
  · omega
  · exact (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)


noncomputable def tripleMeasure (width : ℕ) :=
  (fairBlockMeasure width).prod ((fairBlockMeasure width).prod (fairBlockMeasure width))

instance (width : ℕ) : IsProbabilityMeasure (tripleMeasure width) := by
  unfold tripleMeasure
  infer_instance

theorem tripleMeasure_apply (width : ℕ)
    (event : Set ((Fin width → Bool) × (Fin width → Bool) × (Fin width → Bool))) :
    tripleMeasure width event = ∫⁻ first, ∫⁻ second,
      fairBlockMeasure width {third | (first, second, third) ∈ event}
        ∂fairBlockMeasure width ∂fairBlockMeasure width := by
  rw [tripleMeasure, Measure.prod_apply (Set.to_countable _ |>.measurableSet)]
  apply lintegral_congr
  intro first
  exact Measure.prod_apply (Set.to_countable _ |>.measurableSet)

theorem lintegral_tripleValue_length (M : Machine Unit Bool α) (i time sourceWidth bound : ℕ)
    (enough : bound ≤ sourceWidth)
    (short : ∀ bits word, cappedCall M i time bits = some word → word.length ≤ bound) :
    (∫⁻ bits, (optionLength (tripleValue M i time sourceWidth bound bits) : ℝ≥0∞)
      ∂tripleMeasure sourceWidth) =
      (i : ℝ≥0∞) * tripleMeasure sourceWidth
        {bits | (tripleValue M i time sourceWidth bound bits).isSome} := by
  conv_lhs => rw [tripleMeasure, lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp_rw [lintegral_prod _ (measurable_of_countable _).aemeasurable]
  simp only [tripleValue]
  simp_rw [lintegral_balance_length sourceWidth i bound _ _ enough
    (short _) (short _)]
  rw [tripleMeasure_apply]
  simp only [Set.mem_ofPred_eq]
  simp_rw [lintegral_const_mul _ (measurable_of_countable _)]

/-- Padding past the two source blocks and selector block leaves their exact
actual-stream law unchanged. -/
theorem fairBlockMeasure_value_event (M : Machine Unit Bool α)
    (i time sourceWidth selectorWidth totalWidth : ℕ)
    (sourcePositive : 0 < sourceWidth) (selectorFits : selectorWidth ≤ sourceWidth)
    (totalFits : 2 * sourceWidth + selectorWidth ≤ totalWidth)
    (event : Option (List α) → Prop) :
    fairBlockMeasure totalWidth {bits | event (value M i time sourceWidth selectorWidth (List.ofFn bits))} =
      tripleMeasure sourceWidth {bits | event (tripleValue M i time sourceWidth selectorWidth bits)} := by
  classical
  have totalPositive : 0 < totalWidth := by omega
  rw [← fairCoinMeasure_fixedBlock_event totalWidth totalPositive 0 _
    (Set.to_countable _ |>.measurableSet)]
  have blockPrefix : ∀ stream, List.ofFn (fixedBlock totalWidth stream 0) = streamPrefix stream totalWidth := by
    intro stream
    congr 1
    funext index
    simp [fixedBlock]
  change fairCoinMeasure {stream | event (value M i time sourceWidth selectorWidth
    (List.ofFn (fixedBlock totalWidth stream 0)))} = _
  simp_rw [blockPrefix, value_streamPrefix_eq_triple M i time sourceWidth selectorWidth totalWidth selectorFits totalFits]
  change fairCoinMeasure ((fixedBlockTriple sourceWidth) ⁻¹' {bits |
    event (tripleValue M i time sourceWidth selectorWidth bits)}) = _
  rw [← Measure.map_apply (by
    exact ((measurable_fixedBlocks sourceWidth).eval (a := 0)).prodMk
      (((measurable_fixedBlocks sourceWidth).eval (a := 1)).prodMk
        ((measurable_fixedBlocks sourceWidth).eval (a := 2))))
    (Set.to_countable _ |>.measurableSet), fairCoinMeasure_map_fixedBlockTriple sourceWidth sourcePositive]
  rfl


theorem tripleMeasure_ge_weighted_rectangle (width : ℕ)
    (event : Set ((Fin width → Bool) × (Fin width → Bool) × (Fin width → Bool)))
    (firstEvent secondEvent : Set (Fin width → Bool)) (weight : ℝ≥0∞)
    (lower : ∀ first ∈ firstEvent, ∀ second ∈ secondEvent,
      weight ≤ fairBlockMeasure width {third | (first, second, third) ∈ event}) :
    weight * fairBlockMeasure width firstEvent * fairBlockMeasure width secondEvent ≤
      tripleMeasure width event := by
  classical
  have inner : ∀ first,
      (∫⁻ second, firstEvent.indicator (fun _ => secondEvent.indicator (fun _ => weight) second) first
        ∂fairBlockMeasure width) =
        firstEvent.indicator (fun _ => weight * fairBlockMeasure width secondEvent) first := by
    intro first
    by_cases member : first ∈ firstEvent
    · simp only [Set.indicator_of_mem member]
      exact lintegral_indicator_const (Set.to_countable _ |>.measurableSet) _
    · simp [Set.indicator_of_notMem member]
  calc
    weight * fairBlockMeasure width firstEvent * fairBlockMeasure width secondEvent =
        ∫⁻ first, ∫⁻ second,
          firstEvent.indicator (fun _ => secondEvent.indicator (fun _ => weight) second) first
            ∂fairBlockMeasure width ∂fairBlockMeasure width := by
      simp_rw [inner]
      rw [lintegral_indicator_const (Set.to_countable _ |>.measurableSet)]
      ring
    _ ≤ ∫⁻ first, ∫⁻ second,
        fairBlockMeasure width {third | (first, second, third) ∈ event}
          ∂fairBlockMeasure width ∂fairBlockMeasure width := by
      apply lintegral_mono
      intro first
      apply lintegral_mono
      intro second
      by_cases one : first ∈ firstEvent
      · by_cases two : second ∈ secondEvent
        · simpa only [Set.indicator_of_mem one, Set.indicator_of_mem two] using lower first one second two
        · simp [Set.indicator_of_notMem two, Set.indicator_of_mem one]
      · simp [Set.indicator_of_notMem one]
    _ = tripleMeasure width event := (tripleMeasure_apply width event).symm

def cappedLengthEvent (M : Machine Unit Bool α) (i time width : ℕ) (relation : ℕ → Prop) : Set (Fin width → Bool) :=
  {bits | ∃ word, cappedCall M i time (List.ofFn bits) = some word ∧ relation word.length}

theorem cappedLengthEvent_measure (M : Machine Unit Bool α) (i time width : ℕ)
    (enough : time < width) (relation : ℕ → Prop) :
    fairBlockMeasure width (cappedLengthEvent M i time width relation) =
      fairCoinMeasure (M.boundedPrefixLengthEvent (generatorData i) relation time) := by
  rw [← fairCoinMeasure_fixedBlock_event width (by omega) 0 _
    (Set.to_countable _ |>.measurableSet)]
  congr 1
  ext stream
  have blockPrefix : List.ofFn (fixedBlock width stream 0) = streamPrefix stream width := by
    congr 1
    funext index
    simp [fixedBlock]
  have run : M.run (generatorData i) (streamPrefix stream width) time =
      M.run (generatorData i) (streamPrefix stream (time + 1)) time :=
    M.run_streamPrefix_eq_of_not_exhausted (generatorData i)
      (stream_mem_prefix_cylinder stream (time + 1)) enough
      (M.run_not_exhausted_of_length _ _ time (by simp))
  simp only [Set.mem_ofPred_eq, cappedLengthEvent, Machine.boundedPrefixLengthEvent,
    blockPrefix, cappedCall_eq_some, run]


theorem tripleValue_middle_success_lower (M : Machine Unit Bool α)
    (i time width bound : ℕ) :
    (fairBlockMeasure width (cappedLengthEvent M i time width (fun n => n = i))) ^ 2 ≤
      tripleMeasure width {bits | (tripleValue M i time width bound bits).isSome} := by
  have lower := tripleMeasure_ge_weighted_rectangle width
    {bits | (tripleValue M i time width bound bits).isSome}
    (cappedLengthEvent M i time width (fun n => n = i))
    (cappedLengthEvent M i time width (fun n => n = i)) 1 (by
      intro first one second two
      obtain ⟨left, leftRun, leftLength⟩ := one
      obtain ⟨right, rightRun, rightLength⟩ := two
      simp [tripleValue, leftRun, rightRun, balance, leftLength, rightLength])
  simpa [pow_two] using lower

theorem tripleValue_strict_success_lower (M : Machine Unit Bool α)
    (i time width bound : ℕ) (enough : bound ≤ width)
    (short : ∀ bits word, cappedCall M i time bits = some word → word.length ≤ bound) :
    (2 : ℝ≥0∞)⁻¹ *
        fairBlockMeasure width (cappedLengthEvent M i time width (fun n => n < i)) *
        fairBlockMeasure width (cappedLengthEvent M i time width (fun n => i < n)) ≤
      tripleMeasure width {bits | (tripleValue M i time width bound bits).isSome} := by
  apply tripleMeasure_ge_weighted_rectangle
  intro first one second two
  obtain ⟨left, leftRun, leftLength⟩ := one
  obtain ⟨right, rightRun, rightLength⟩ := two
  simpa only [Set.mem_ofPred_eq, tripleValue, leftRun, rightRun] using
    balance_strict_success_ge_half width i bound left right leftLength rightLength
      (short _ right rightRun) enough

theorem inverse_bracketing_constant (bound : ℕ) :
    (2 : ℝ≥0∞)⁻¹ * ((1 : ℝ≥0∞) / (8 * bound)) * ((1 : ℝ≥0∞) / (8 * bound)) =
      (1 : ℝ≥0∞) / (128 * (bound : ℝ≥0∞) ^ 2) := by
  simp only [one_div]
  have finite8 : 8 * (bound : ℝ≥0∞) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) (by simp)
  have finite16 : 2 * (8 * (bound : ℝ≥0∞)) ≠ ∞ := ENNReal.mul_ne_top (by norm_num) finite8
  rw [← ENNReal.mul_inv (Or.inr finite8) (Or.inl (by norm_num)),
    ← ENNReal.mul_inv (Or.inr finite8) (Or.inl finite16)]
  congr 1
  ring


theorem lintegral_value_length (M : Machine Unit Bool α)
    (i time sourceWidth bound totalWidth : ℕ)
    (sourcePositive : 0 < sourceWidth) (selectorFits : bound ≤ sourceWidth)
    (totalFits : 2 * sourceWidth + bound ≤ totalWidth)
    (short : ∀ bits word, cappedCall M i time bits = some word → word.length ≤ bound) :
    (∫⁻ bits, (optionLength (value M i time sourceWidth bound (List.ofFn bits)) : ℝ≥0∞)
      ∂fairBlockMeasure totalWidth) =
      (i : ℝ≥0∞) * fairBlockMeasure totalWidth
        {bits | (value M i time sourceWidth bound (List.ofFn bits)).isSome} := by
  have lengthMap : (fairBlockMeasure totalWidth).map
      (fun bits => optionLength (value M i time sourceWidth bound (List.ofFn bits))) =
      (tripleMeasure sourceWidth).map (fun bits => optionLength (tripleValue M i time sourceWidth bound bits)) := by
    apply Measure.ext_of_singleton
    intro length
    rw [Measure.map_apply (measurable_of_countable _) (measurableSet_singleton length),
      Measure.map_apply (measurable_of_countable _) (measurableSet_singleton length)]
    exact fairBlockMeasure_value_event M i time sourceWidth bound totalWidth sourcePositive selectorFits totalFits
      (fun answer => optionLength answer = length)
  calc
    (∫⁻ bits, (optionLength (value M i time sourceWidth bound (List.ofFn bits)) : ℝ≥0∞)
      ∂fairBlockMeasure totalWidth) = ∫⁻ length : ℕ, (length : ℝ≥0∞)
        ∂(fairBlockMeasure totalWidth).map (fun bits => optionLength (value M i time sourceWidth bound (List.ofFn bits))) :=
      (lintegral_map (measurable_of_countable _) (measurable_of_countable _)).symm
    _ = ∫⁻ bits, (optionLength (tripleValue M i time sourceWidth bound bits) : ℝ≥0∞)
        ∂tripleMeasure sourceWidth := by
      rw [lengthMap, lintegral_map (measurable_of_countable _) (measurable_of_countable _)]
    _ = (i : ℝ≥0∞) * tripleMeasure sourceWidth
        {bits | (tripleValue M i time sourceWidth bound bits).isSome} :=
      lintegral_tripleValue_length M i time sourceWidth bound selectorFits short
    _ = _ := by
      congr 1
      exact (fairBlockMeasure_value_event M i time sourceWidth bound totalWidth sourcePositive selectorFits totalFits
        (fun answer => answer.isSome = true)).symm


theorem cappedCall_mem_layer [Fintype α] (G : UniformGenerators α) (i time : ℕ)
    (bits : BitString) (word : List α) (accepted : cappedCall G.machine i time bits = some word) :
    word ∈ G.layer i := by
  have run := (cappedCall_eq_some G.machine i time bits word).mp accepted
  refine ⟨bits ++ [false], by simp, time, ?_⟩
  rw [G.machine.run_append_of_not_exhausted (generatorData i) bits [false] time (by simp [run]), run]

theorem cappedCall_length_le [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i time : ℕ) (bits : BitString) (word : List α)
    (accepted : cappedCall G.machine i time bits = some word) : word.length ≤ p i := by
  obtain ⟨fast, _, run⟩ := short i word (cappedCall_mem_layer G i time bits word accepted)
  exact G.machine.accepted_output_length_le _ fast (p i) word run

/-- A complete bounded phase succeeds with inverse-polynomial probability.
This bound uses actual capped native calls and the actual fair-coin block law. -/
theorem value_success_lower [Fintype α] (G : UniformGenerators α)
    (mean : G.ExpectedLength) (p : PolynomialBound)
    (runtime : ∀ n, (G.layer n).Nonempty → G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞))
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i sourceWidth totalWidth : ℕ) (active : i ∈ G.activeIndices)
    (sourceFits : 8 * p i * p i < sourceWidth)
    (totalFits : 2 * sourceWidth + p i ≤ totalWidth) :
    (1 : ℝ≥0∞) / (128 * (p i : ℝ≥0∞) ^ 2) ≤
      fairBlockMeasure totalWidth {bits |
        (value G.machine i (8 * p i * p i) sourceWidth (p i) (List.ofFn bits)).isSome} := by
  have positive := p.positive i
  have selectorFits : p i ≤ sourceWidth := by nlinarith
  rw [fairBlockMeasure_value_event G.machine i (8 * p i * p i) sourceWidth (p i) totalWidth
    (by omega) selectorFits totalFits (fun answer => answer.isSome = true)]
  have dichotomy := G.expected_length_bounded_prefix_bracketing mean p runtime short i active
  rw [← cappedLengthEvent_measure G.machine i (8 * p i * p i) sourceWidth sourceFits (fun n => n = i),
    ← cappedLengthEvent_measure G.machine i (8 * p i * p i) sourceWidth sourceFits (fun n => n < i),
    ← cappedLengthEvent_measure G.machine i (8 * p i * p i) sourceWidth sourceFits (fun n => i < n)] at dichotomy
  rw [← inverse_bracketing_constant]
  rcases dichotomy with middle | ⟨below, above⟩
  · apply le_trans _ (tripleValue_middle_success_lower G.machine i (8 * p i * p i) sourceWidth (p i))
    have small : (1 : ℝ≥0∞) / (8 * p i) ≤ (1 : ℝ≥0∞) / 4 := by
      simp only [one_div]
      apply ENNReal.inv_le_inv.mpr
      have oneLe : (1 : ℝ≥0∞) ≤ p i := by exact_mod_cast positive
      calc
        (4 : ℝ≥0∞) ≤ 8 := by norm_num
        _ = 8 * 1 := by simp
        _ ≤ 8 * (p i : ℝ≥0∞) := by gcongr
    calc
      (2 : ℝ≥0∞)⁻¹ * ((1 : ℝ≥0∞) / (8 * p i)) * ((1 : ℝ≥0∞) / (8 * p i)) ≤
          1 * ((1 : ℝ≥0∞) / 4) * ((1 : ℝ≥0∞) / 4) := by gcongr; norm_num
      _ ≤ (fairBlockMeasure sourceWidth (cappedLengthEvent G.machine i (8 * p i * p i) sourceWidth (fun n => n = i))) ^ 2 := by
        simp only [one_mul, pow_two]
        gcongr
  · apply le_trans _ (tripleValue_strict_success_lower G.machine i (8 * p i * p i) sourceWidth (p i)
      selectorFits (cappedCall_length_le G p short i (8 * p i * p i)))
    gcongr


theorem supported_length_event_nonempty [Fintype α] (G : UniformGenerators α)
    (i : ℕ) (active : i ∈ G.activeIndices) (relation : ℕ → Prop)
    (positive : 0 < fairCoinMeasure {stream | relation (G.machine.streamLength (generatorData i) stream)}) :
    ∃ word, word ∈ G.layer i ∧ relation word.length := by
  have productive := (G.machine.generator_probability_one_iff_nonempty
    (generatorData i) (G.isGenerator i)).mpr active
  have negligible : fairCoinMeasure (G.machine.acceptedStreams (generatorData i))ᶜ = 0 := by
    rw [measure_compl (G.machine.measurableSet_acceptedStreams (generatorData i))
      (measure_ne_top _ _), measure_univ, productive]
    simp
  by_contra absent
  have subset : {stream | relation (G.machine.streamLength (generatorData i) stream)} ⊆
      (G.machine.acceptedStreams (generatorData i))ᶜ := by
    intro stream member accepted
    obtain ⟨bits, cylinderMember, word, produces⟩ := accepted
    have generated : word ∈ G.layer i :=
      ⟨bits ++ [false], by simp, G.machine.produces_append (generatorData i) bits [false] word produces⟩
    have same := G.machine.streamLength_of_produces (generatorData i) ⟨bits, cylinderMember, produces⟩
    exact absent ⟨word, generated, by simpa only [Set.mem_ofPred_eq, same] using member⟩
  have zero := measure_mono (μ := fairCoinMeasure) subset
  rw [negligible] at zero
  exact not_le_of_gt positive zero

theorem supported_length_event_positive [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i : ℕ) (word : List α) (member : word ∈ G.layer i) (relation : ℕ → Prop)
    (holds : relation word.length) :
    0 < fairCoinMeasure {stream | relation (G.machine.streamLength (generatorData i) stream)} := by
  apply (G.supported_word_bounded_prefix_mass_pos p short i word member).trans_le
  apply measure_mono
  intro stream run
  have same := G.machine.streamLength_of_produces (generatorData i)
    ⟨streamPrefix stream (8 * p i * p i + 1), stream_mem_prefix_cylinder _ _, 8 * p i * p i, run⟩
  simpa only [Set.mem_ofPred_eq, same] using holds

theorem supported_word_opposite_above [Fintype α] (G : UniformGenerators α)
    (mean : G.ExpectedLength) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i : ℕ) (word : List α) (member : word ∈ G.layer i) (below : word.length < i) :
    ∃ upper, upper ∈ G.layer i ∧ i < upper.length := by
  have active : i ∈ G.activeIndices := ⟨word, member⟩
  have lowPositive := supported_length_event_positive G p short i word member (fun n => n < i) below
  have balance := (G.expected_length_tail_balance mean p short i active).1
  have highPositive : 0 < fairCoinMeasure {stream | i < G.machine.streamLength (generatorData i) stream} := by
    by_contra absent
    have zero : fairCoinMeasure {stream | i < G.machine.streamLength (generatorData i) stream} = 0 :=
      le_antisymm (not_lt.mp absent) bot_le
    rw [zero, mul_zero] at balance
    exact not_le_of_gt lowPositive balance
  exact supported_length_event_nonempty G i active (fun n => i < n) highPositive

theorem supported_word_opposite_below [Fintype α] (G : UniformGenerators α)
    (mean : G.ExpectedLength) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i : ℕ) (word : List α) (member : word ∈ G.layer i) (above : i < word.length) :
    ∃ lower, lower ∈ G.layer i ∧ lower.length < i := by
  have active : i ∈ G.activeIndices := ⟨word, member⟩
  have highPositive := supported_length_event_positive G p short i word member (fun n => i < n) above
  have balance := (G.expected_length_tail_balance mean p short i active).2
  have lowPositive : 0 < fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream < i} := by
    by_contra absent
    have zero : fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream < i} = 0 :=
      le_antisymm (not_lt.mp absent) bot_le
    rw [zero, mul_zero] at balance
    exact not_le_of_gt highPositive balance
  exact supported_length_event_nonempty G i active (fun n => n < i) lowPositive


theorem cappedCall_finite_witness [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i time width : ℕ) (later : p i ≤ time) (enough : time < width)
    (word : List α) (member : word ∈ G.layer i) :
    ∃ bits : Fin width → Bool, cappedCall G.machine i time (List.ofFn bits) = some word := by
  obtain ⟨fast, _, accepted⟩ := short i word member
  let stream : BitStream := fun index => fast.getD index false
  have cylinderMember : stream ∈ cylinder fast := by
    intro index
    exact List.getD_eq_getElem fast false index.isLt
  have atTime : G.machine.run (generatorData i) fast time = .halted (.accepted word) := by
    simpa only [Nat.add_sub_of_le later] using
      G.machine.run_halted_add (generatorData i) fast (p i) _ accepted (time - p i)
  refine ⟨fun index => stream index.val, ?_⟩
  apply (cappedCall_eq_some G.machine i time _ word).mpr
  change G.machine.run (generatorData i) (streamPrefix stream width) time = _
  rw [G.machine.run_streamPrefix_eq_of_not_exhausted (generatorData i) cylinderMember enough
    (by simp [atTime]), atTime]

theorem choose_true_finite_witness (width denominator numerator : ℕ)
    (large : 1 < denominator) (positive : 0 < numerator) (ordered : numerator ≤ denominator)
    (enough : Nat.clog 2 denominator ≤ width) :
    ∃ bits : Fin width → Bool,
      Simulation.WordStack.RationalSelection.choose denominator numerator (List.ofFn bits) = some true := by
  have mass : 0 < fairBlockMeasure width {bits |
      Simulation.WordStack.RationalSelection.choose denominator numerator (List.ofFn bits) = some true} := by
    rw [fairBlockMeasure_choose_true width denominator numerator large ordered enough]
    exact ENNReal.div_pos (by exact_mod_cast positive.ne') (by simp)
  exact nonempty_of_measure_ne_zero mass.ne'

theorem choose_false_finite_witness (width denominator numerator : ℕ)
    (large : 1 < denominator) (ordered : numerator < denominator)
    (enough : Nat.clog 2 denominator ≤ width) :
    ∃ bits : Fin width → Bool,
      Simulation.WordStack.RationalSelection.choose denominator numerator (List.ofFn bits) = some false := by
  have mass : 0 < fairBlockMeasure width {bits |
      Simulation.WordStack.RationalSelection.choose denominator numerator (List.ofFn bits) = some false} := by
    rw [fairBlockMeasure_choose_false width denominator numerator large ordered.le enough]
    exact ENNReal.div_pos (by exact_mod_cast (Nat.sub_pos_of_lt ordered).ne') (by simp)
  exact nonempty_of_measure_ne_zero mass.ne'

/-- Full support is retained even for arbitrarily rare strict tails. The
opposite word is obtained from the source mean; every word has a fast path. -/
theorem tripleValue_supported_word_witness [Fintype α] (G : UniformGenerators α)
    (mean : G.ExpectedLength) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i width : ℕ) (enough : 8 * p i * p i < width)
    (word : List α) (member : word ∈ G.layer i) :
    ∃ bits, tripleValue G.machine i (8 * p i * p i) width (p i) bits = some word := by
  have positive := p.positive i
  have later : p i ≤ 8 * p i * p i := by nlinarith
  have wordBound : word.length ≤ p i := by
    obtain ⟨fast, _, accepted⟩ := short i word member
    exact G.machine.accepted_output_length_le _ fast (p i) word accepted
  obtain ⟨wordBits, wordRun⟩ := cappedCall_finite_witness G p short i _ width later enough word member
  rcases lt_trichotomy word.length i with below | equal | above
  · obtain ⟨upper, upperMember, upperLength⟩ := supported_word_opposite_above G mean p short i word member below
    obtain ⟨upperBits, upperRun⟩ := cappedCall_finite_witness G p short i _ width later enough upper upperMember
    have upperBound := cappedCall_length_le G p short i _ _ upper upperRun
    have logFits : Nat.clog 2 (upper.length - word.length) ≤ width :=
      (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
    obtain ⟨selector, choice⟩ := choose_true_finite_witness width (upper.length - word.length) (upper.length - i)
      (by omega) (by omega) (by omega) logFits
    refine ⟨(wordBits, upperBits, selector), ?_⟩
    simp only [tripleValue, wordRun, upperRun]
    rw [balance_take_eq i (p i) (some word) (some upper) _
      (by intro w same; cases same; exact wordBound)
      (by intro w same; cases same; exact upperBound)]
    simp [balance, below.ne, below, upperLength, choice]
  · refine ⟨(wordBits, wordBits, fun _ => false), ?_⟩
    simp [tripleValue, wordRun, balance, equal]
  · obtain ⟨lower, lowerMember, lowerLength⟩ := supported_word_opposite_below G mean p short i word member above
    obtain ⟨lowerBits, lowerRun⟩ := cappedCall_finite_witness G p short i _ width later enough lower lowerMember
    have lowerBound := cappedCall_length_le G p short i _ _ lower lowerRun
    have logFits : Nat.clog 2 (word.length - lower.length) ≤ width :=
      (Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide : 1 < 2)))).trans (by omega)
    obtain ⟨selector, choice⟩ := choose_false_finite_witness width (word.length - lower.length) (word.length - i)
      (by omega) (by omega) logFits
    refine ⟨(lowerBits, wordBits, selector), ?_⟩
    simp only [tripleValue, lowerRun, wordRun]
    rw [balance_take_eq i (p i) (some lower) (some word) _
      (by intro w same; cases same; exact lowerBound)
      (by intro w same; cases same; exact wordBound)]
    simp [balance, lowerLength.ne, lowerLength, above, choice]


theorem tripleMeasure_singleton_pos (width : ℕ)
    (bits : (Fin width → Bool) × (Fin width → Bool) × (Fin width → Bool)) :
    0 < tripleMeasure width {bits} := by
  rcases bits with ⟨first, second, third⟩
  have singleton : {(first, second, third)} = {first} ×ˢ ({second} ×ˢ {third}) := by simp
  rw [tripleMeasure, singleton, Measure.prod_prod, Measure.prod_prod,
    fairBlockMeasure_singleton, fairBlockMeasure_singleton, fairBlockMeasure_singleton]
  have positive : (0 : ℝ≥0∞) < (2 : ℝ≥0∞)⁻¹ ^ width :=
    bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0))
  exact ENNReal.mul_pos_iff.mpr ⟨positive, ENNReal.mul_pos_iff.mpr ⟨positive, positive⟩⟩

theorem value_mem_layer [Fintype α] (G : UniformGenerators α) (i time sourceWidth selectorWidth : ℕ)
    (bits : BitString) (word : List α)
    (accepted : value G.machine i time sourceWidth selectorWidth bits = some word) :
    word ∈ G.layer i := by
  rcases balance_returns_input i _ _ _ word accepted with first | second
  · exact cappedCall_mem_layer G i time _ word first
  · exact cappedCall_mem_layer G i time _ word second

/-- The bounded phase has exactly the source layer as its positive-probability
support. No minimum source-word probability is required. -/
theorem value_word_probability_pos_iff [Fintype α] (G : UniformGenerators α)
    (mean : G.ExpectedLength) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i sourceWidth totalWidth : ℕ)
    (sourceFits : 8 * p i * p i < sourceWidth)
    (totalFits : 2 * sourceWidth + p i ≤ totalWidth) (word : List α) :
    0 < fairBlockMeasure totalWidth {bits |
      value G.machine i (8 * p i * p i) sourceWidth (p i) (List.ofFn bits) = some word} ↔
      word ∈ G.layer i := by
  constructor
  · intro positive
    obtain ⟨bits, accepted⟩ := nonempty_of_measure_ne_zero positive.ne'
    exact value_mem_layer G i _ sourceWidth (p i) _ word accepted
  · intro member
    have positive := p.positive i
    have selectorFits : p i ≤ sourceWidth := by nlinarith
    rw [fairBlockMeasure_value_event G.machine i (8 * p i * p i) sourceWidth (p i) totalWidth
      (by omega) selectorFits totalFits (fun answer => answer = some word)]
    obtain ⟨bits, accepted⟩ := tripleValue_supported_word_witness G mean p short i sourceWidth sourceFits word member
    apply (tripleMeasure_singleton_pos sourceWidth bits).trans_le
    apply measure_mono
    intro other same
    have equal : other = bits := same
    simpa only [equal, Set.mem_ofPred_eq] using accepted

theorem value_supported_word_witness [Fintype α] (G : UniformGenerators α)
    (mean : G.ExpectedLength) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i sourceWidth totalWidth : ℕ)
    (sourceFits : 8 * p i * p i < sourceWidth)
    (totalFits : 2 * sourceWidth + p i ≤ totalWidth) (word : List α) (member : word ∈ G.layer i) :
    ∃ bits : Fin totalWidth → Bool,
      value G.machine i (8 * p i * p i) sourceWidth (p i) (List.ofFn bits) = some word :=
  nonempty_of_measure_ne_zero ((value_word_probability_pos_iff G mean p short i sourceWidth totalWidth
    sourceFits totalFits word).mpr member).ne'

end BalancedPairPhase

end ComplexityOfGenerators
