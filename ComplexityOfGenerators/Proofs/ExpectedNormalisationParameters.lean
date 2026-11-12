import ComplexityOfGenerators.Foundations.BalancedPairProbability
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Family

/-! Concrete polynomial block sizes and the statistical facts used by the
native balanced-pair normalisation. No phase-machine correctness is assumed here. -/
namespace ComplexityOfGenerators.ExpectedNormalisation
open MeasureTheory
open scoped ENNReal
noncomputable section


def squareMultiple (factor : ℕ) (positive : 0 < factor) (p : PolynomialBound) : PolynomialBound :=
  (⟨factor, 0, positive⟩ : PolynomialBound).mul (p.mul p)

@[simp] theorem squareMultiple_eval (factor : ℕ) (positive : 0 < factor) (p : PolynomialBound) (n : ℕ) :
    squareMultiple factor positive p n = factor * (p n)^2 := by
  unfold squareMultiple
  rw [PolynomialBound.mul_eval, PolynomialBound.mul_eval]
  have constant : (⟨factor, 0, positive⟩ : PolynomialBound) n = factor := by simp [PolynomialBound.eval]
  rw [constant]
  ring

def sourceTime (p : PolynomialBound) : PolynomialBound := squareMultiple 8 (by decide) p
def sourceSeed (p : PolynomialBound) : PolynomialBound := squareMultiple 9 (by decide) p
def blockWidth (p : PolynomialBound) : PolynomialBound := squareMultiple 33 (by decide) p
def reciprocal (p : PolynomialBound) : PolynomialBound := squareMultiple 128 (by decide) p

@[simp] theorem sourceTime_eval (p : PolynomialBound) (n : ℕ) : sourceTime p n = 8*p n*p n := by
  simp [sourceTime]
  ring

theorem block_fits (p : PolynomialBound) (n : ℕ) :
    8*p n*p n < sourceSeed p n ∧ 2*sourceSeed p n+p n ≤ blockWidth p n ∧ p n ≤ sourceSeed p n := by
  have positive := p.positive n
  simp only [sourceSeed, blockWidth, squareMultiple_eval]
  constructor
  · nlinarith
  · constructor <;> nlinarith

variable {α : Type} [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))

def phaseValue (n : ℕ) (bits : BitString) : Option (List α) :=
  BalancedPairPhase.value G.machine n (sourceTime p n) (sourceSeed p n) (p n) bits

include short in
theorem capped_length (n : ℕ) (bits : BitString) (word : List α)
    (output : BalancedPairPhase.cappedCall G.machine n (sourceTime p n) bits = some word) : word.length ≤ p n :=
  BalancedPairPhase.cappedCall_length_le G p short n _ bits word output

include short in
theorem phase_mean (n : ℕ) :
    (∫⁻ bits, Simulation.FixedBlockRetry.phaseLength (blockWidth p) (phaseValue G p) n bits ∂fairBlockMeasure (blockWidth p n)) =
      n * fairBlockMeasure (blockWidth p n) (Simulation.FixedBlockRetry.successSet (blockWidth p) (phaseValue G p) n) := by
  have lengths (bits : Fin (blockWidth p n) → Bool) :
      Simulation.FixedBlockRetry.phaseLength (blockWidth p) (phaseValue G p) n bits =
        (BalancedPairPhase.optionLength (phaseValue G p n (List.ofFn bits)) : ℝ≥0∞) := by
    unfold Simulation.FixedBlockRetry.phaseLength
    cases phaseValue G p n (List.ofFn bits) <;> rfl
  simp_rw [lengths]
  exact BalancedPairPhase.lintegral_value_length G.machine n _ _ _ _ ((sourceSeed p).positive n)
    (block_fits p n).2.2 (block_fits p n).2.1 (capped_length G p short n)

include short in
theorem phase_support (mean : G.ExpectedLength) (n : ℕ) :
    {word | ∃ bits : BitString, bits.length = blockWidth p n ∧ phaseValue G p n bits = some word} = G.layer n := by
  ext word
  constructor
  · rintro ⟨bits, _, output⟩
    exact BalancedPairPhase.value_mem_layer G n _ _ _ bits word output
  · intro member
    obtain ⟨bits, output⟩ := BalancedPairPhase.value_supported_word_witness G mean p short n
      (sourceSeed p n) (blockWidth p n) (block_fits p n).1 (block_fits p n).2.1 word member
    refine ⟨List.ofFn bits, by simp, ?_⟩
    simpa only [phaseValue, sourceTime_eval] using output

include short in
theorem phase_mass (mean : G.ExpectedLength)
    (runtime : ∀ n, (G.layer n).Nonempty → G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞))
    (n : ℕ) (active : (G.layer n).Nonempty) :
    (reciprocal p n : ℝ≥0∞)⁻¹ ≤ fairBlockMeasure (blockWidth p n)
      (Simulation.FixedBlockRetry.successSet (blockWidth p) (phaseValue G p) n) := by
  have lower := BalancedPairPhase.value_success_lower G mean p runtime short n (sourceSeed p n) (blockWidth p n)
    active (block_fits p n).1 (block_fits p n).2.1
  have denominator : (reciprocal p n : ℝ≥0∞) = 128*(p n : ℝ≥0∞)^2 := by
    simp [reciprocal, Nat.cast_mul, Nat.cast_pow]
  rw [denominator]
  simpa only [one_div, Simulation.FixedBlockRetry.successSet, phaseValue, sourceTime_eval] using lower

end
end ComplexityOfGenerators.ExpectedNormalisation
