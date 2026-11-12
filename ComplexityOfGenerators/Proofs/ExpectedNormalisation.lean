import ComplexityOfGenerators.Proofs.ExpectedNormalisationParameters
import ComplexityOfGenerators.Simulation.BalancedPairGenerator
import ComplexityOfGenerators.Simulation.FixedBlockRetry.BoundedView

/-! A concrete native normalisation of expected-length generators. Independent
bounded balanced phases preserve full support and target mean; geometric retry
moments justify the actual quadratic native compiler using first moments only. -/
namespace ComplexityOfGenerators.ExpectedNormalisation
open Simulation WordStack
open UnionGenerator (Symbol)
open scoped ENNReal
noncomputable section

variable {α : Type} [Fintype α] (G : UniformGenerators α) (p : PolynomialBound)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))

noncomputable def nativeCap : PolynomialBound :=
  BalancedPairGenerator.phaseCap (sourceSeed p) (sourceTime p) (blockWidth p) p

noncomputable def nativeTime : PolynomialBound :=
  BalancedPairGenerator.phaseTime G.machine (sourceSeed p) (sourceTime p) (blockWidth p) p

noncomputable def nativePhase := BalancedPairGenerator.phase G.machine (sourceSeed p) (sourceTime p)

include short in
theorem correct : FixedBlockRetry.PhaseCorrect (Symbol.unit : BalancedPairGenerator.Cell G.machine) Symbol.bit
    (UnionGenerator.outputLetter G.machine G.machine) (blockWidth p) (nativePhase G p) (phaseValue G p) :=
  BalancedPairGenerator.phase_correct G.machine (sourceSeed p) (sourceTime p) (blockWidth p) p
    (fun n => (block_fits p n).2.1) (capped_length G p short)

include short in
theorem bounded : FixedBlockRetry.PhaseBound Symbol.bit (blockWidth p) (nativeCap p) (nativeTime G p) (nativePhase G p) :=
  BalancedPairGenerator.phase_bound G.machine (sourceSeed p) (sourceTime p) (blockWidth p) p
    (fun n => (block_fits p n).2.1) (capped_length G p short)

theorem master (s : BalancedPairGenerator.Store G.machine) :
    ((nativePhase G p).eval s 22).length = (s 22).length :=
  congrArg List.length (BalancedPairGenerator.phase_fixes22 G.machine (sourceSeed p) (sourceTime p) s)

theorem budgets (n : ℕ) : n+1 ≤ nativeCap p n ∧ blockWidth p n ≤ nativeCap p n :=
  ⟨BalancedPairGenerator.phase_indexBudget (sourceSeed p) (sourceTime p) (blockWidth p) p n,
    BalancedPairGenerator.phase_widthBudget (sourceSeed p) (sourceTime p) (blockWidth p) p n⟩

/-- The actual compiled finite-control retry machine. -/
noncomputable def normalised : UniformGenerators α :=
  FixedBlockRetry.family Symbol.unit Symbol.bit (UnionGenerator.outputLetter G.machine G.machine)
    (blockWidth p) (nativeCap p) (nativeTime G p) (nativePhase G p) (phaseValue G p)
    (correct G p short) (bounded G p short) (master G p) (budgets p)

include short in
theorem normalised_layer (mean : G.ExpectedLength) (n : ℕ) :
    (normalised G p short).layer n = G.layer n := by
  unfold normalised
  rw [FixedBlockRetry.family_layer]
  exact phase_support G p short mean n

include short in
theorem normalised_language (mean : G.ExpectedLength) : (normalised G p short).language = G.language := by
  ext word
  change (∃ n, word ∈ (normalised G p short).layer n) ↔ ∃ n, word ∈ G.layer n
  simp only [normalised_layer G p short mean]

include short in
theorem normalised_expectedLength : (normalised G p short).ExpectedLength :=
  FixedBlockRetry.family_expectedLength Symbol.unit Symbol.bit (UnionGenerator.outputLetter G.machine G.machine)
    (blockWidth p) (nativeCap p) (nativeTime G p) (nativePhase G p) (phaseValue G p)
    (correct G p short) (bounded G p short) (master G p) (budgets p) (phase_mean G p short)

include short in
theorem normalised_expectedPolynomialTime (mean : G.ExpectedLength)
    (runtime : ∀ n, (G.layer n).Nonempty → G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) :
    (normalised G p short).ExpectedPolynomialTime := by
  apply FixedBlockRetry.family_expectedPolynomialTime Symbol.unit Symbol.bit (UnionGenerator.outputLetter G.machine G.machine)
    (blockWidth p) (nativeCap p) (nativeTime G p) (nativePhase G p) (phaseValue G p)
    (correct G p short) (bounded G p short) (master G p) (budgets p) (reciprocal p)
  intro n phaseActive
  obtain ⟨bits, length, word, output⟩ := phaseActive
  have active : (G.layer n).Nonempty := ⟨word, by rw [← phase_support G p short mean n]; exact ⟨bits, length, output⟩⟩
  exact phase_mass G p short mean runtime n active

include short in
theorem normalised_coverage (mean : G.ExpectedLength) (coverage : G.PolynomialIndexCoverage) :
    (normalised G p short).PolynomialIndexCoverage := by
  obtain ⟨bound, coverage⟩ := coverage
  refine ⟨bound, fun word member => ?_⟩
  rw [normalised_language G p short mean] at member
  obtain ⟨index, small, produced⟩ := coverage word member
  exact ⟨index, small, by rw [normalised_layer G p short mean]; exact produced⟩

noncomputable def boundedClock : PolynomialBound :=
  FixedBlockRetry.singleClock (blockWidth p) (nativeCap p) (nativeTime G p)

include short in
/-- One bounded native source call is exactly one independent balanced phase,
including its failures. This is the interface reused by positive closures. -/
theorem normalised_bounded_view (n : ℕ) (bits : BitString) (length : bits.length = blockWidth p n) :
    UnionGenerator.sourceValue (normalised G p short).machine (boundedClock G p) n bits = phaseValue G p n bits :=
  FixedBlockRetry.sourceValue_full_block Symbol.unit Symbol.bit (UnionGenerator.outputLetter G.machine G.machine)
    (blockWidth p) (nativeCap p) (nativeTime G p) (nativePhase G p) (phaseValue G p)
    (correct G p short) (bounded G p short) (master G p) n bits (budgets p n).1 (budgets p n).2 length

end
end ComplexityOfGenerators.ExpectedNormalisation
