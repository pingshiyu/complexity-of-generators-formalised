import ComplexityOfGenerators.Foundations.StreamSemantics
import ComplexityOfGenerators.Foundations.LengthSlices

/-!
# Expected length and expected polynomial time

These definitions use the original uniform native machine and the fair-coin
measure. Length is zero on divergence; runtime is infinite there. As in the
manuscript, runtime is bounded in expectation on nonempty layers, and every
supported word retains a polynomially short accepting execution. ELEPG is
restricted to infinite languages. No variance or prescribed-distribution
assumption is imposed.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

namespace UniformGenerators

variable {α : Type} [Fintype α]

def ExpectedLength (G : UniformGenerators α) : Prop :=
  ∀ n, G.machine.expectedLength (generatorData n) = (n : ℝ≥0∞)

def ExpectedPolynomialTime (G : UniformGenerators α) : Prop :=
  ∃ p : PolynomialBound,
    (∀ n, (G.layer n).Nonempty →
      G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) ∧
    (∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))

end UniformGenerators

def ELEPG (α : Type) [Fintype α] : LanguageClass α :=
  { L | L.Infinite ∧ ∃ G : UniformGenerators α,
      G.language = L ∧ G.ExpectedLength ∧ G.ExpectedPolynomialTime }

namespace GeneratorFamily

variable {α : Type} [Fintype α] (G : GeneratorFamily α)

theorem expectedLength_of_nonempty_layers
    (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time)
    (nonempty : ∀ n, (G.toUniformGenerators.layer n).Nonempty) :
    G.toUniformGenerators.ExpectedLength := by
  intro n
  have length (stream : BitStream) : G.machine.streamLength (generatorData n) stream = n := by
    let bits := streamPrefix stream (seed n)
    have bitsLength : bits.length = seed n := streamPrefix_length stream _
    obtain ⟨word, produces⟩ := ((bound n).2 bits bitsLength).mpr (nonempty n)
    have member : word ∈ G.toUniformGenerators.layer n := by
      refine ⟨bits, ?_, produces⟩
      intro empty
      have positive := seed.positive n
      simp [empty] at bitsLength
      omega
    exact (G.machine.streamLength_of_produces (generatorData n)
      ⟨bits, stream_mem_prefix_cylinder stream (seed n), produces⟩).trans
        (G.outputLength n word member)
  simp [Machine.expectedLength, length]

theorem expectedPolynomialTime_of_polynomialTime
    (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time) :
    G.toUniformGenerators.ExpectedPolynomialTime := by
  refine ⟨time, ?_, ?_⟩
  · intro n nonempty
    apply lintegral_le_const
    filter_upwards [] with stream
    let bits := streamPrefix stream (seed n)
    have bitsLength : bits.length = seed n := streamPrefix_length stream _
    obtain ⟨word, produces⟩ := ((bound n).2 bits bitsLength).mpr nonempty
    have run := G.machine.produces_at_bound (generatorData n) bits (time n) word
      ((bound n).1 bits bitsLength.le) produces
    exact G.machine.streamRuntime_le_of_acceptsBy (generatorData n)
      ⟨bits, word, stream_mem_prefix_cylinder stream (seed n), run⟩
  · intro n word member
    obtain ⟨bits, length, run⟩ := (G.machine.generatedLanguage_iff_budget_seed
      (generatorData n) (seed n) (time n) (seed.positive n) (bound n) word).mp member
    refine ⟨bits, ?_, run⟩
    intro empty
    have positive := seed.positive n
    simp [empty] at length
    omega

end GeneratorFamily

/-- Exact-length polynomial generators whose every slice is nonempty also
provide mean-exact expected-length generators, on the very same native machine. -/
theorem pg_mem_elepg_of_nonempty_slices {α : Type} [Fintype α] {L : Language α}
    (pg : L ∈ PG α) (slices : ∀ n, (lengthSlice L n).Nonempty) : L ∈ ELEPG α := by
  obtain ⟨G, language, seed, time, bound⟩ := pg
  have nonempty (n : ℕ) : (G.toUniformGenerators.layer n).Nonempty := by
    rw [G.layer_eq_lengthSlice, language]
    exact slices n
  exact ⟨language_infinite_of_nonempty_slices L slices, G.toUniformGenerators, language,
    G.expectedLength_of_nonempty_layers seed time bound nonempty,
    G.expectedPolynomialTime_of_polynomialTime seed time bound⟩

end ComplexityOfGenerators
