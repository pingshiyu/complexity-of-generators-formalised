import ComplexityOfGenerators.Simulation.BoundedMachinePhase
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Family
import ComplexityOfGenerators.Foundations.FiniteBlockPhases
import ComplexityOfGenerators.Proofs.ExpectedNormalisation

/-! Bounded native phases are a common intermediate representation for expected
closures. Retrying is an implemented constructor; every record carries an actual
finite-control machine and proved fair-block mean/success bounds. -/
namespace ComplexityOfGenerators
open Simulation MeasureTheory
open scoped ENNReal
noncomputable section

structure BoundedPhaseFamily (α : Type) [Fintype α] where
  machine : Machine Unit Bool α
  seed : PolynomialBound
  clock : PolynomialBound
  reciprocal : PolynomialBound
  mean : ∀ n, OptionPhase.HasMean (fairBlockMeasure (seed n))
    (fun bits => UnionGenerator.sourceValue machine clock n (List.ofFn bits)) n
  mass : ∀ n, (∃ bits : Fin (seed n) → Bool, ∃ word,
      UnionGenerator.sourceValue machine clock n (List.ofFn bits) = some word) →
    (reciprocal n : ℝ≥0∞)⁻¹ ≤ fairBlockMeasure (seed n)
      {bits | (UnionGenerator.sourceValue machine clock n (List.ofFn bits)).isSome}

namespace BoundedPhaseFamily
variable {α : Type} [Fintype α] (P : BoundedPhaseFamily α)

def phase (n : ℕ) : FiniteBlockPhase α :=
  ⟨P.seed n, fun bits => UnionGenerator.sourceValue P.machine P.clock n (List.ofFn bits)⟩

def layer (n : ℕ) : Language α := (P.phase n).language

noncomputable def repeated : UniformGenerators α :=
  FixedBlockRetry.family UnionGenerator.Symbol.unit UnionGenerator.Symbol.bit
    (UnionGenerator.outputLetter P.machine P.machine) P.seed (BoundedMachinePhase.cap P.seed P.clock)
    (BoundedMachinePhase.time P.machine P.seed P.clock) (BoundedMachinePhase.phase P.machine P.seed P.clock)
    (fun n bits => UnionGenerator.sourceValue P.machine P.clock n bits)
    (BoundedMachinePhase.phase_correct P.machine P.seed P.clock)
    (BoundedMachinePhase.phase_bound P.machine P.seed P.clock)
    (fun s => congrArg List.length (BoundedMachinePhase.phase_fixes22 P.machine P.seed P.clock s))
    (fun n => ⟨BoundedMachinePhase.indexBudget P.seed P.clock n, BoundedMachinePhase.widthBudget P.seed P.clock n⟩)

theorem layer_iff (n : ℕ) (word : List α) : word ∈ P.layer n ↔
    ∃ bits : Fin (P.seed n) → Bool, UnionGenerator.sourceValue P.machine P.clock n (List.ofFn bits) = some word := by
  exact fairBlockMeasure_event_pos_iff _ _

theorem repeated_layer (n : ℕ) : P.repeated.layer n = P.layer n := by
  unfold repeated
  rw [FixedBlockRetry.family_layer]
  ext word
  rw [layer_iff]
  constructor
  · rintro ⟨bits, length, output⟩
    let vector := (blockListEquiv (P.seed n)).symm ⟨bits, length⟩
    have recovered : List.ofFn vector = bits := congrArg Subtype.val ((blockListEquiv (P.seed n)).apply_symm_apply ⟨bits, length⟩)
    exact ⟨vector, by simpa only [recovered] using output⟩
  · rintro ⟨bits, output⟩
    exact ⟨List.ofFn bits, by simp, output⟩

theorem repeated_expectedLength : P.repeated.ExpectedLength := by
  apply FixedBlockRetry.family_expectedLength
  intro n
  have lengths (bits : Fin (P.seed n) → Bool) :
      FixedBlockRetry.phaseLength P.seed (fun n bits => UnionGenerator.sourceValue P.machine P.clock n bits) n bits =
        (BalancedPairPhase.optionLength (UnionGenerator.sourceValue P.machine P.clock n (List.ofFn bits)) : ℝ≥0∞) := by
    unfold FixedBlockRetry.phaseLength
    dsimp only
    cases UnionGenerator.sourceValue P.machine P.clock n (List.ofFn bits) <;> rfl
  simp_rw [lengths]
  exact P.mean n

theorem repeated_expectedPolynomialTime : P.repeated.ExpectedPolynomialTime := by
  apply FixedBlockRetry.family_expectedPolynomialTime _ _ _ _ _ _ _ _ _ _ _ _ P.reciprocal
  intro n active
  obtain ⟨bits, length, word, output⟩ := active
  let vector := (blockListEquiv (P.seed n)).symm ⟨bits, length⟩
  have recovered : List.ofFn vector = bits := congrArg Subtype.val ((blockListEquiv (P.seed n)).apply_symm_apply ⟨bits, length⟩)
  exact P.mass n ⟨vector, word, by simpa only [recovered] using output⟩

end BoundedPhaseFamily

namespace ExpectedNormalisation
variable {α : Type} [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))
    (mean : G.ExpectedLength)
    (runtime : ∀ n, (G.layer n).Nonempty → G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞))

include short mean runtime in
noncomputable def boundedFamily : BoundedPhaseFamily α where
  machine := (normalised G p short).machine
  seed := blockWidth p
  clock := boundedClock G p
  reciprocal := reciprocal p
  mean := by
    intro n
    unfold OptionPhase.HasMean OptionPhase.success
    simp_rw [normalised_bounded_view G p short n (List.ofFn _) List.length_ofFn]
    have lengths (bits : Fin (blockWidth p n) → Bool) :
        (BalancedPairPhase.optionLength (phaseValue G p n (List.ofFn bits)) : ℝ≥0∞) =
          FixedBlockRetry.phaseLength (blockWidth p) (phaseValue G p) n bits := by
      unfold FixedBlockRetry.phaseLength
      cases phaseValue G p n (List.ofFn bits) <;> rfl
    simp_rw [lengths]
    exact phase_mean G p short n
  mass := by
    intro n active
    obtain ⟨bits, word, output⟩ := active
    rw [normalised_bounded_view G p short n (List.ofFn _) List.length_ofFn] at output
    have sourceActive : (G.layer n).Nonempty := by
      refine ⟨word, ?_⟩
      rw [← phase_support G p short mean n]
      exact ⟨List.ofFn bits, by simp, output⟩
    simpa only [FixedBlockRetry.successSet, normalised_bounded_view G p short n (List.ofFn _) List.length_ofFn] using
      phase_mass G p short mean runtime n sourceActive

include short mean runtime in
theorem boundedFamily_layer (n : ℕ) : (boundedFamily G p short mean runtime).layer n = G.layer n := by
  ext word
  rw [BoundedPhaseFamily.layer_iff]
  dsimp only [boundedFamily]
  simp_rw [normalised_bounded_view G p short n (List.ofFn _) List.length_ofFn]
  constructor
  · rintro ⟨bits, output⟩
    rw [← phase_support G p short mean n]
    exact ⟨List.ofFn bits, by simp, output⟩
  · intro member
    obtain ⟨bits, output⟩ := BalancedPairPhase.value_supported_word_witness G mean p short n
      (sourceSeed p n) (blockWidth p n) (block_fits p n).1 (block_fits p n).2.1 word member
    exact ⟨bits, by simpa only [phaseValue, sourceTime_eval] using output⟩

end ExpectedNormalisation
namespace BoundedPhaseFamily
variable {α : Type} [Fintype α]

noncomputable def ofExpected (G : UniformGenerators α) (mean : G.ExpectedLength)
    (expected : G.ExpectedPolynomialTime) : BoundedPhaseFamily α :=
  ExpectedNormalisation.boundedFamily G (Classical.choose expected)
    (Classical.choose_spec expected).2 mean (Classical.choose_spec expected).1

theorem ofExpected_layer (G : UniformGenerators α) (mean : G.ExpectedLength)
    (expected : G.ExpectedPolynomialTime) (n : ℕ) : (ofExpected G mean expected).layer n = G.layer n :=
  ExpectedNormalisation.boundedFamily_layer G (Classical.choose expected)
    (Classical.choose_spec expected).2 mean (Classical.choose_spec expected).1 n

end BoundedPhaseFamily

end
end ComplexityOfGenerators
