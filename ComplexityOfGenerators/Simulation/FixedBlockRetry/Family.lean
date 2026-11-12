import ComplexityOfGenerators.Simulation.FixedBlockRetry.Native
import ComplexityOfGenerators.Foundations.FiniteBlockProbability
import ComplexityOfGenerators.ExpectedGenerators

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry
open WordStack MeasureTheory
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {S O : Type} [Fintype S] [Fintype O]

/-- Every finite block event is measurable in the actual product law. -/
theorem measurable_successSet (width : PolynomialBound) (f : ℕ → BitString → Option (List O)) (n : ℕ) :
    MeasurableSet (successSet width f n) := (Set.toFinite _).measurableSet

theorem success_mass_pos_iff (width : PolynomialBound) (f : ℕ → BitString → Option (List O)) (n : ℕ) :
    0 < fairBlockMeasure (width n) (successSet width f n) ↔
      ∃ block : BitString, block.length = width n ∧ ∃ word, f n block = some word := by
  constructor
  · intro positive
    have nonempty : (successSet width f n).Nonempty := by
      by_contra empty
      have equal := Set.not_nonempty_iff_eq_empty.mp empty
      rw [equal, measure_empty] at positive
      exact lt_irrefl _ positive
    obtain ⟨block, hit⟩ := nonempty
    obtain ⟨word, output⟩ := Option.isSome_iff_exists.mp hit
    exact ⟨List.ofFn block, by simp, word, output⟩
  · rintro ⟨block, length, word, output⟩
    let vector := (blockListEquiv (width n)).symm ⟨block, length⟩
    have recovered : List.ofFn vector = block := congrArg Subtype.val ((blockListEquiv (width n)).apply_symm_apply ⟨block, length⟩)
    have member : vector ∈ successSet width f n := by simp [successSet, recovered, output]
    have lower := measure_mono (μ := fairBlockMeasure (width n)) (Set.singleton_subset_iff.mpr member)
    rw [fairBlockMeasure_singleton] at lower
    have positive : 0 < (2 : ℝ≥0∞)⁻¹ ^ width n :=
      bot_lt_iff_ne_bot.mpr (pow_ne_zero _ (by norm_num))
    exact positive.trans_le lower

variable (unitSymbol : S) (bitSymbol : Bool → S) (decode : S → Option O)
    (width cap time : PolynomialBound) (phase : WordStack.Routine S O 35)
    (f : ℕ → BitString → Option (List O))
    (correct : PhaseCorrect unitSymbol bitSymbol decode width phase f)
    (bounded : PhaseBound bitSymbol width cap time phase)
    (frame : ∀ s, (phase.eval s 22).length = (s 22).length)
    (budgets : ∀ n, n+1 ≤ cap n ∧ width n ≤ cap n)

include correct bounded frame budgets in
theorem machine_generator (n : ℕ) :
    (machine unitSymbol bitSymbol decode width phase).IsGenerator (generatorData n) := by
  let M := machine unitSymbol bitSymbol decode width phase
  have halting := machine_halting unitSymbol bitSymbol decode width cap time phase f correct bounded frame
    n (budgets n).1 (budgets n).2
  by_cases active : ∃ block : BitString, block.length = width n ∧ ∃ word, f n block = some word
  · exact M.isGenerator_of_fixedBlock_retries (generatorData n) (width n) (width.positive n)
      (successSet width f n) (measurable_successSet width f n) ((success_mass_pos_iff width f n).mpr active)
      (25*(coefficient width cap time n)^2) halting
      (first_success_acceptsBy unitSymbol bitSymbol decode width cap time phase f correct bounded frame
        n (budgets n).1 (budgets n).2)
  · refine ⟨halting, Or.inr ?_⟩
    have empty : M.generatedLanguage (generatorData n) = ∅ := by
      rw [machine_language unitSymbol bitSymbol decode width cap time phase f correct bounded frame n (budgets n).1 (budgets n).2]
      apply Set.eq_empty_iff_forall_notMem.mpr
      rintro word ⟨block, length, output⟩
      exact active ⟨block, length, word, output⟩
    rw [(M.acceptedStreams_eq_empty_iff (generatorData n)).mpr empty, measure_empty]

def family : UniformGenerators O where
  machine := machine unitSymbol bitSymbol decode width phase
  isGenerator := machine_generator unitSymbol bitSymbol decode width cap time phase f correct bounded frame budgets

theorem family_layer (n : ℕ) :
    (family unitSymbol bitSymbol decode width cap time phase f correct bounded frame budgets).layer n =
      {word | ∃ block : BitString, block.length = width n ∧ f n block = some word} :=
  machine_language unitSymbol bitSymbol decode width cap time phase f correct bounded frame n (budgets n).1 (budgets n).2

def phaseLength (n : ℕ) (block : Fin (width n) → Bool) : ℝ≥0∞ :=
  (((f n (List.ofFn block)).map List.length).getD 0 : ℕ)

include correct bounded frame budgets in
theorem family_streamLength (n : ℕ) (stream : BitStream)
    (hit : fixedBlock (width n) stream (firstSuccessIndex (width n) (successSet width f n) stream) ∈ successSet width f n) :
    (machine unitSymbol bitSymbol decode width phase).streamLength (generatorData n) stream =
      phaseLength width f n (selectedBlock (width n) (successSet width f n) stream) := by
  obtain ⟨word, output, phaseOutput⟩ := value_first_success_prefix width f n stream hit
  let bits := streamPrefix stream ((firstSuccessIndex (width n) (successSet width f n) stream+1)*width n)
  have produced := (machine_produces_iff unitSymbol bitSymbol decode width cap time phase f correct bounded frame
    n bits word (budgets n).1 (budgets n).2).mpr output
  have length := (machine unitSymbol bitSymbol decode width phase).streamLength_of_produces (generatorData n)
    ⟨bits, stream_mem_prefix_cylinder stream _, produced⟩
  rw [length]
  simp only [phaseLength, selectedBlock, phaseOutput, Option.map_some, Option.getD_some]

include correct bounded frame budgets in
theorem family_expectedLength
    (mean : ∀ n, (∫⁻ block, phaseLength width f n block ∂fairBlockMeasure (width n)) =
      n * fairBlockMeasure (width n) (successSet width f n)) :
    (family unitSymbol bitSymbol decode width cap time phase f correct bounded frame budgets).ExpectedLength := by
  intro n active
  have positive : 0 < fairBlockMeasure (width n) (successSet width f n) := by
    apply (success_mass_pos_iff width f n).mpr
    obtain ⟨word, member⟩ := active
    rw [family_layer] at member
    obtain ⟨block, length, output⟩ := member
    exact ⟨block, length, word, output⟩
  apply Machine.fixedBlock_retry_expectedLength _ _ (width n) (width.positive n)
    (successSet width f n) (measurable_successSet width f n) positive (phaseLength width f n)
    (measurable_of_countable _) _ n (mean n)
    (family_streamLength unitSymbol bitSymbol decode width cap time phase f correct bounded frame budgets n)
  intro block absent
  unfold successSet at absent
  cases output : f n (List.ofFn block) <;> simp_all [phaseLength]

noncomputable def expectedClock (reciprocal : PolynomialBound) : PolynomialBound :=
  PolynomialBound.ofPolynomial (50*(coefficient width cap time).asPolynomial^2*reciprocal.asPolynomial^2 +
    25*(coefficient width cap time).asPolynomial^2)

theorem expectedClock_lower (reciprocal : PolynomialBound) (n : ℕ) :
    50*(coefficient width cap time n)^2*(reciprocal n)^2+25*(coefficient width cap time n)^2 ≤
      expectedClock width cap time reciprocal n := by
  have upper := PolynomialBound.eval_le_ofPolynomial
    (50*(coefficient width cap time).asPolynomial^2*reciprocal.asPolynomial^2 +
      25*(coefficient width cap time).asPolynomial^2) n
  simpa only [expectedClock, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, PolynomialBound.asPolynomial_eval] using upper

include correct bounded frame budgets in
theorem family_expectedPolynomialTime (reciprocal : PolynomialBound)
    (lower : ∀ n, (∃ block : BitString, block.length = width n ∧ ∃ word, f n block = some word) →
      (reciprocal n : ℝ≥0∞)⁻¹ ≤ fairBlockMeasure (width n) (successSet width f n)) :
    (family unitSymbol bitSymbol decode width cap time phase f correct bounded frame budgets).ExpectedPolynomialTime := by
  refine ⟨expectedClock width cap time reciprocal, ?_, ?_⟩
  · intro n active
    obtain ⟨word, member⟩ := active
    rw [family_layer] at member
    obtain ⟨block, length, output⟩ := member
    have existsOutput : ∃ block : BitString, block.length = width n ∧ ∃ word, f n block = some word :=
      ⟨block, length, word, output⟩
    have positive := (success_mass_pos_iff width f n).mpr existsOutput
    have bound := (machine unitSymbol bitSymbol decode width phase).fixedBlock_retry_runtime_of_inverse_mass
      (generatorData n) (width n) (width.positive n) (successSet width f n) (measurable_successSet width f n)
      positive (25*(coefficient width cap time n)^2) (reciprocal n) (lower n existsOutput)
      (first_success_acceptsBy unitSymbol bitSymbol decode width cap time phase f correct bounded frame n (budgets n).1 (budgets n).2)
    apply bound.trans
    apply Nat.cast_le.mpr
    have clock := expectedClock_lower width cap time reciprocal n
    nlinarith
  · intro n word member
    rw [family_layer] at member
    obtain ⟨block, length, output⟩ := member
    have accepted := machine_short_path unitSymbol bitSymbol decode width cap time phase f correct bounded frame
      n block word (budgets n).1 (budgets n).2 length output
    have clock := expectedClock_lower width cap time reciprocal n
    have later : 25*(coefficient width cap time n)^2 ≤ expectedClock width cap time reciprocal n := by omega
    refine ⟨block, ?_, ?_⟩
    · intro empty
      have positive := width.positive n
      simp [empty] at length
      omega
    · have padded := (machine unitSymbol bitSymbol decode width phase).run_halted_add (generatorData n) block
        (25*(coefficient width cap time n)^2) (.accepted word) accepted
        (expectedClock width cap time reciprocal n-25*(coefficient width cap time n)^2)
      rw [Nat.add_sub_of_le later] at padded
      exact padded

end
end ComplexityOfGenerators.Simulation.FixedBlockRetry
