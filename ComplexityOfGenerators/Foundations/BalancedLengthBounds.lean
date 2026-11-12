import ComplexityOfGenerators.Foundations.ExpectedClosureBounds

/-! First-moment bounds for bounded output lengths.  The strict lower and
upper tails around the mean either both have inverse-polynomial mass, or the
atom at the mean has constant mass.  The native bounded-prefix consequence
uses only the existing runtime event-subtraction estimate. -/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

theorem bounded_nat_mean_tail_balance {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (length : Ω → ℕ)
    (measurable : Measurable length) (i B : ℕ)
    (bounded : ∀ x, length x ≤ B)
    (mean : (∫⁻ x, (length x : ℝ≥0∞) ∂μ) = (i : ℝ≥0∞)) :
    μ {x | length x < i} ≤ (B : ℝ≥0∞) * μ {x | i < length x} ∧
      μ {x | i < length x} ≤ (B : ℝ≥0∞) * μ {x | length x < i} := by
  classical
  let low := {x | length x < i}
  let high := {x | i < length x}
  have lowMeasurable : MeasurableSet low := measurableSet_lt measurable measurable_const
  have highMeasurable : MeasurableSet high := measurableSet_lt measurable_const measurable
  have lengthMeasurable : Measurable (fun x => (length x : ℝ≥0∞)) :=
    (measurable_of_countable _).comp measurable
  have indexBound : i ≤ B := by
    have upper : (i : ℝ≥0∞) ≤ (B : ℝ≥0∞) := by
      rw [← mean]
      apply lintegral_le_const
      exact Filter.Eventually.of_forall (fun x => by exact_mod_cast bounded x)
    exact_mod_cast upper
  have below (x : Ω) :
      (length x : ℝ≥0∞) + low.indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        (i : ℝ≥0∞) + high.indicator (fun _ => (B : ℝ≥0∞)) x := by
    by_cases lower : length x < i
    · have outside : ¬ i < length x := by omega
      have h : (length x : ℝ≥0∞) + 1 ≤ (i : ℝ≥0∞) := by
        exact_mod_cast (show length x + 1 ≤ i by omega)
      simpa [low, high, lower, outside] using h
    · by_cases upper : i < length x
      · have h : (length x : ℝ≥0∞) ≤ (i : ℝ≥0∞) + B := by
          exact_mod_cast (show length x ≤ i + B by have := bounded x; omega)
        simpa [low, high, lower, upper] using h
      · have equal : length x = i := by omega
        simp [low, high, equal]
  have above (x : Ω) :
      (i : ℝ≥0∞) + high.indicator (fun _ => (1 : ℝ≥0∞)) x ≤
        (length x : ℝ≥0∞) + low.indicator (fun _ => (B : ℝ≥0∞)) x := by
    by_cases lower : length x < i
    · have outside : ¬ i < length x := by omega
      have h : (i : ℝ≥0∞) ≤ (length x : ℝ≥0∞) + B := by
        exact_mod_cast (show i ≤ length x + B by omega)
      simpa [low, high, lower, outside] using h
    · by_cases upper : i < length x
      · have h : (i : ℝ≥0∞) + 1 ≤ (length x : ℝ≥0∞) := by
          exact_mod_cast (show i + 1 ≤ length x by omega)
        simpa [low, high, lower, upper] using h
      · have equal : length x = i := by omega
        simp [low, high, equal]
  constructor
  · have integral := lintegral_mono (μ := μ) below
    rw [lintegral_add_left lengthMeasurable,
      lintegral_add_left measurable_const,
      lintegral_indicator_const lowMeasurable,
      lintegral_indicator_const highMeasurable, mean] at integral
    simp only [one_mul, lintegral_const, measure_univ, mul_one] at integral
    exact (WithTop.add_le_add_iff_left (by simp : (i : ℝ≥0∞) ≠ ⊤)).mp integral
  · have integral := lintegral_mono (μ := μ) above
    rw [lintegral_add_left measurable_const,
      lintegral_add_left lengthMeasurable,
      lintegral_indicator_const highMeasurable,
      lintegral_indicator_const lowMeasurable, mean] at integral
    simp only [one_mul, lintegral_const, measure_univ, mul_one] at integral
    exact (WithTop.add_le_add_iff_left (by simp : (i : ℝ≥0∞) ≠ ⊤)).mp integral

theorem three_mass_tail_dichotomy (a z c : ℝ≥0∞) (B : ℕ) (positive : 0 < B)
    (total : a + z + c = 1)
    (below : a ≤ (B : ℝ≥0∞) * c) (above : c ≤ (B : ℝ≥0∞) * a) :
    (1 : ℝ≥0∞) / 2 ≤ z ∨
      (1 : ℝ≥0∞) / (4 * B) ≤ a ∧ (1 : ℝ≥0∞) / (4 * B) ≤ c := by
  by_cases middle : (1 : ℝ≥0∞) / 2 ≤ z
  · exact Or.inl middle
  · have small : z ≤ (1 : ℝ≥0∞) / 2 := le_of_not_ge middle
    have tails : (1 : ℝ≥0∞) / 2 ≤ a + c := by
      have upper : (1 : ℝ≥0∞) / 2 + (1 : ℝ≥0∞) / 2 ≤ (a + c) + (1 : ℝ≥0∞) / 2 := by
        calc
          (1 : ℝ≥0∞) / 2 + (1 : ℝ≥0∞) / 2 = 1 := ENNReal.add_halves 1
          _ = a + z + c := total.symm
          _ ≤ _ := by simpa only [add_assoc, add_comm, add_left_comm] using add_le_add_left small (a + c)
      exact (WithTop.add_le_add_iff_right (by norm_num : (1 : ℝ≥0∞) / 2 ≠ ⊤)).mp upper
    have lower (x y : ℝ≥0∞) (sum : (1 : ℝ≥0∞) / 2 ≤ x + y)
        (balanced : y ≤ (B : ℝ≥0∞) * x) : (1 : ℝ≥0∞) / (4 * B) ≤ x := by
      have oneLe : (1 : ℝ≥0∞) ≤ B := by exact_mod_cast positive
      have self : x ≤ (B : ℝ≥0∞) * x := by
        calc
          x = 1 * x := (one_mul _).symm
          _ ≤ _ := by gcongr
      have half : (1 : ℝ≥0∞) / 2 ≤ (2 * B) * x := by
        calc
          (1 : ℝ≥0∞) / 2 ≤ x + y := sum
          _ ≤ (B : ℝ≥0∞) * x + (B : ℝ≥0∞) * x := add_le_add self balanced
          _ = _ := by ring
      apply (ENNReal.div_le_iff (by positivity : (4 : ℝ≥0∞) * B ≠ 0)
        (ENNReal.mul_ne_top (by norm_num) (by simp))).mpr
      calc
        (1 : ℝ≥0∞) = 2 * ((1 : ℝ≥0∞) / 2) := by
          rw [div_eq_mul_inv, one_mul, ENNReal.mul_inv_cancel (by norm_num) (by norm_num)]
        _ ≤ 2 * ((2 * B) * x) := by gcongr
        _ = _ := by ring
    exact Or.inr ⟨lower a c tails above, lower c a (by simpa [add_comm] using tails) below⟩

/-- A bounded natural random variable with integer mean either has a large
atom at its mean or has quantitatively nonempty strict tails on both sides. -/
theorem bounded_nat_mean_dichotomy {Ω : Type} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (length : Ω → ℕ)
    (measurable : Measurable length) (i B : ℕ) (positive : 0 < B)
    (bounded : ∀ x, length x ≤ B)
    (mean : (∫⁻ x, (length x : ℝ≥0∞) ∂μ) = (i : ℝ≥0∞)) :
    (1 : ℝ≥0∞) / 2 ≤ μ {x | length x = i} ∨
      (1 : ℝ≥0∞) / (4 * B) ≤ μ {x | length x < i} ∧
      (1 : ℝ≥0∞) / (4 * B) ≤ μ {x | i < length x} := by
  let low := {x | length x < i}
  let middle := {x | length x = i}
  let high := {x | i < length x}
  have middleMeasurable : MeasurableSet middle := measurableSet_eq_fun measurable measurable_const
  have highMeasurable : MeasurableSet high := measurableSet_lt measurable_const measurable
  have firstDisjoint : Disjoint low middle := by
    rw [Set.disjoint_left]
    intro x lower equal
    change length x < i at lower
    change length x = i at equal
    omega
  have secondDisjoint : Disjoint (low ∪ middle) high := by
    rw [Set.disjoint_left]
    intro x lower higher
    change i < length x at higher
    rcases lower with lower | equal
    · change length x < i at lower; omega
    · change length x = i at equal; omega
  have whole : (low ∪ middle) ∪ high = Set.univ := by
    ext x
    simp only [low, middle, high, Set.mem_union, Set.mem_ofPred_eq, Set.mem_univ, iff_true]
    omega
  have total : μ low + μ middle + μ high = 1 := by
    rw [← measure_union firstDisjoint middleMeasurable,
      ← measure_union secondDisjoint highMeasurable, whole, measure_univ]
  obtain ⟨below, above⟩ := bounded_nat_mean_tail_balance μ length measurable i B bounded mean
  exact three_mass_tail_dichotomy (μ low) (μ middle) (μ high) B positive total below above

namespace Machine

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

/-- A predicate on the length returned by a genuine bounded native call. -/
def boundedPrefixLengthEvent (relation : ℕ → Prop) (time : ℕ) : Set BitStream :=
  {stream | ∃ word, M.run data (streamPrefix stream (time + 1)) time = .halted (.accepted word) ∧ relation word.length}

theorem boundedPrefixLengthEvent_eq (relation : ℕ → Prop) (time : ℕ) :
    M.boundedPrefixLengthEvent data relation time =
      {stream | relation (M.streamLength data stream)} ∩
        {stream | M.streamRuntime data stream ≤ (time : ℝ≥0∞)} := by
  ext stream
  constructor
  · rintro ⟨word, accepted, related⟩
    have produces : M.streamProduces data stream word :=
      ⟨streamPrefix stream (time + 1), stream_mem_prefix_cylinder stream (time + 1), time, accepted⟩
    refine ⟨?_, M.streamRuntime_le_of_acceptsBy data
      ⟨streamPrefix stream (time + 1), word, stream_mem_prefix_cylinder stream (time + 1), accepted⟩⟩
    simpa only [M.streamLength_of_produces data produces, Set.mem_ofPred_eq] using related
  · intro member
    obtain ⟨word, accepted, length⟩ := M.streamLength_run_streamPrefix_of_runtime_le data member.2
    exact ⟨word, accepted, by simpa only [length, Set.mem_ofPred_eq] using member.1⟩

theorem measurableSet_boundedPrefixLengthEvent (relation : ℕ → Prop) (time : ℕ) :
    MeasurableSet (M.boundedPrefixLengthEvent data relation time) := by
  have description : {stream | relation (M.streamLength data stream)} =
      ⋃ n : ℕ, ⋃ (_ : relation n), {stream | M.streamLength data stream = n} := by
    ext stream
    simp
  have relationMeasurable : MeasurableSet {stream | relation (M.streamLength data stream)} := by
    rw [description]
    exact MeasurableSet.iUnion fun n => MeasurableSet.iUnion fun _ =>
      (M.measurable_streamLength data) (measurableSet_singleton n)
  rw [M.boundedPrefixLengthEvent_eq data]
  exact relationMeasurable.inter (measurableSet_le (M.measurable_streamRuntime data) measurable_const)

/-- Every fixed accepting path survives every larger clock with positive
fair-coin mass.  No quantitative lower bound on that word's mass is required. -/
theorem bounded_prefix_word_mass_pos (bits : BitString) (word : List O) (first time : ℕ)
    (accepted : M.run data bits first = .halted (.accepted word)) (later : first ≤ time) :
    0 < fairCoinMeasure {stream |
      M.run data (streamPrefix stream (time + 1)) time = .halted (.accepted word)} := by
  have atTime : M.run data bits time = .halted (.accepted word) := by
    simpa only [Nat.add_sub_of_le later] using M.run_halted_add data bits first _ accepted (time - first)
  have positive : 0 < fairCoinMeasure (cylinder bits) := by
    rw [fairCoinMeasure_cylinder]
    exact bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num : (2 : ℝ≥0∞)⁻¹ ≠ 0))
  apply positive.trans_le
  apply measure_mono
  intro stream member
  exact M.run_on_streamPrefix_of_accepting_prefix data member atTime

theorem measure_boundedPrefixLengthEvent_ge_half (relation : ℕ → Prop)
    (p δ : ℝ≥0∞) (time : ℕ) (positive : 0 < time)
    (expected : M.expectedRuntime data ≤ p)
    (mass : δ ≤ fairCoinMeasure {stream | relation (M.streamLength data stream)})
    (loss : p / (time : ℝ≥0∞) ≤ δ / 2) :
    δ / 2 ≤ fairCoinMeasure (M.boundedPrefixLengthEvent data relation time) := by
  have surviving := measure_joint_runtime_ge_half fairCoinMeasure
    {stream | relation (M.streamLength data stream)} (M.streamRuntime data)
    (M.measurable_streamRuntime data).aemeasurable p (time : ℝ≥0∞) δ expected
    (by exact_mod_cast positive.ne') (by simp) mass
    (ne_top_of_le_ne_top (measure_ne_top _ _) mass) loss
  apply surviving.trans
  apply measure_mono
  intro stream member
  obtain ⟨word, accepted, length⟩ := M.streamLength_run_streamPrefix_of_runtime_le data member.2
  exact ⟨word, accepted, by simpa only [length, Set.mem_ofPred_eq] using member.1⟩

end Machine

namespace UniformGenerators

variable {α : Type} [Fintype α] (G : UniformGenerators α)

/-- The fast-path condition bounds the length of every supported word, hence
also the stream length on every stream, including the zero divergence value. -/
theorem streamLength_le_of_short_paths (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (n : ℕ) (stream : BitStream) : G.machine.streamLength (generatorData n) stream ≤ p n := by
  rcases G.machine.streamLength_spec (generatorData n) stream with produced | ⟨zero, _⟩
  · obtain ⟨word, produces, length⟩ := produced
    obtain ⟨bits, _, accepted⟩ := short n word
      (G.machine.streamProduces_mem_generatedLanguage (generatorData n) produces)
    rw [← length]
    exact G.machine.accepted_output_length_le (generatorData n) bits (p n) word accepted
  · simp [zero]

theorem supported_word_bounded_prefix_mass_pos (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i : ℕ) (word : List α) (member : word ∈ G.layer i) :
    0 < fairCoinMeasure {stream | G.machine.run (generatorData i)
      (streamPrefix stream (8 * p i * p i + 1)) (8 * p i * p i) = .halted (.accepted word)} := by
  obtain ⟨bits, _, accepted⟩ := short i word member
  apply G.machine.bounded_prefix_word_mass_pos (generatorData i) bits word (p i) (8 * p i * p i) accepted
  have positive := p.positive i
  nlinarith

theorem expected_length_tail_balance (mean : G.ExpectedLength) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i : ℕ) (active : i ∈ G.activeIndices) :
    fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream < i} ≤
        (p i : ℝ≥0∞) * fairCoinMeasure {stream | i < G.machine.streamLength (generatorData i) stream} ∧
      fairCoinMeasure {stream | i < G.machine.streamLength (generatorData i) stream} ≤
        (p i : ℝ≥0∞) * fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream < i} :=
  bounded_nat_mean_tail_balance fairCoinMeasure (G.machine.streamLength (generatorData i))
    (G.machine.measurable_streamLength (generatorData i)) i (p i)
    (G.streamLength_le_of_short_paths p short i) (mean i active)

theorem expected_length_tail_dichotomy (mean : G.ExpectedLength) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i : ℕ) (active : i ∈ G.activeIndices) :
    (1 : ℝ≥0∞) / 2 ≤ fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream = i} ∨
      (1 : ℝ≥0∞) / (4 * p i) ≤ fairCoinMeasure {stream | G.machine.streamLength (generatorData i) stream < i} ∧
      (1 : ℝ≥0∞) / (4 * p i) ≤ fairCoinMeasure {stream | i < G.machine.streamLength (generatorData i) stream} :=
  bounded_nat_mean_dichotomy fairCoinMeasure (G.machine.streamLength (generatorData i))
    (G.machine.measurable_streamLength (generatorData i)) i (p i) (p.positive i)
    (G.streamLength_le_of_short_paths p short i) (mean i active)

end UniformGenerators

private theorem balanced_cutoff_ratio (B p : ℕ) (positive : 0 < p) :
    (p : ℝ≥0∞) / ((8 * B * p : ℕ) : ℝ≥0∞) = (1 : ℝ≥0∞) / (8 * B) := by
  simp only [Nat.cast_mul, Nat.cast_ofNat]
  simpa only [one_mul] using ENNReal.mul_div_mul_right 1 (8 * (B : ℝ≥0∞))
    (by exact_mod_cast positive.ne') (by simp)

private theorem balanced_half_four (B : ℕ) :
    ((1 : ℝ≥0∞) / (4 * B)) / 2 = (1 : ℝ≥0∞) / (8 * B) := by
  simp only [div_eq_mul_inv, one_mul]
  rw [← ENNReal.mul_inv (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ 0))]
  congr 1
  ring

private theorem balanced_half_half : ((1 : ℝ≥0∞) / 2) / 2 = (1 : ℝ≥0∞) / 4 := by
  simp only [div_eq_mul_inv, one_mul]
  rw [← ENNReal.mul_inv (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ ⊤))
    (Or.inr (by norm_num : (2 : ℝ≥0∞) ≠ 0))]
  norm_num

namespace UniformGenerators

variable {α : Type} [Fintype α] (G : UniformGenerators α)

/-- The two strict tails retain inverse-polynomial mass after actual bounded
native calls; alternatively the native call returns mean-length words with
constant probability.  Runtime and length need not be independent. -/
theorem expected_length_bounded_prefix_bracketing
    (mean : G.ExpectedLength) (p : PolynomialBound)
    (runtime : ∀ n, (G.layer n).Nonempty → G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞))
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (i : ℕ) (active : i ∈ G.activeIndices) :
    (1 : ℝ≥0∞) / 4 ≤ fairCoinMeasure
        (G.machine.boundedPrefixLengthEvent (generatorData i) (fun length => length = i) (8 * p i * p i)) ∨
      (1 : ℝ≥0∞) / (8 * p i) ≤ fairCoinMeasure
        (G.machine.boundedPrefixLengthEvent (generatorData i) (fun length => length < i) (8 * p i * p i)) ∧
      (1 : ℝ≥0∞) / (8 * p i) ≤ fairCoinMeasure
        (G.machine.boundedPrefixLengthEvent (generatorData i) (fun length => i < length) (8 * p i * p i)) := by
  have positive := p.positive i
  have cutoffPositive : 0 < 8 * p i * p i := by positivity
  have ratio := balanced_cutoff_ratio (p i) (p i) positive
  have expected := runtime i active
  rcases G.expected_length_tail_dichotomy mean p short i active with middle | ⟨below, above⟩
  · left
    have loss : (p i : ℝ≥0∞) / ((8 * p i * p i : ℕ) : ℝ≥0∞) ≤ ((1 : ℝ≥0∞) / 2) / 2 := by
      rw [ratio, balanced_half_half]
      simp only [one_div]
      apply ENNReal.inv_le_inv.mpr
      have oneLe : (1 : ℝ≥0∞) ≤ p i := by exact_mod_cast positive
      calc
        (4 : ℝ≥0∞) ≤ 8 := by norm_num
        _ = 8 * 1 := (mul_one _).symm
        _ ≤ 8 * (p i : ℝ≥0∞) := by gcongr
    have bounded := G.machine.measure_boundedPrefixLengthEvent_ge_half (generatorData i)
      (fun length => length = i) (p i : ℝ≥0∞) ((1 : ℝ≥0∞) / 2)
      (8 * p i * p i) cutoffPositive expected middle loss
    simpa only [balanced_half_half] using bounded
  · right
    have loss : (p i : ℝ≥0∞) / ((8 * p i * p i : ℕ) : ℝ≥0∞) ≤
        ((1 : ℝ≥0∞) / (4 * p i)) / 2 := by
      rw [ratio, balanced_half_four]
    constructor
    · have bounded := G.machine.measure_boundedPrefixLengthEvent_ge_half (generatorData i)
        (fun length => length < i) (p i : ℝ≥0∞) ((1 : ℝ≥0∞) / (4 * p i))
        (8 * p i * p i) cutoffPositive expected below loss
      simpa only [balanced_half_four] using bounded
    · have bounded := G.machine.measure_boundedPrefixLengthEvent_ge_half (generatorData i)
        (fun length => i < length) (p i : ℝ≥0∞) ((1 : ℝ≥0∞) / (4 * p i))
        (8 * p i * p i) cutoffPositive expected above loss
      simpa only [balanced_half_four] using bounded

end UniformGenerators

end ComplexityOfGenerators
