import ComplexityOfGenerators.Foundations.StreamSemanticsProperties
import ComplexityOfGenerators.Foundations.LengthSlices

/-!
# Expected polynomial time and expected length

The moment requirements apply only to nonempty members.  The weaker expected-
length notion has infinitely many nonempty members and no short-path or
producing-index requirement.  EPG retains exact output lengths and polynomially
short accepting paths.  The current ELEPG condition bounds one globally chosen accepting path by
word length; the older per-layer variant is retained as `LayerFastELEPG`.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

namespace UniformGenerators

variable {α : Type} [Fintype α]

def activeIndices (G : UniformGenerators α) : Set ℕ :=
  {n | (G.layer n).Nonempty}

def ExpectedLength (G : UniformGenerators α) : Prop :=
  ∀ n, n ∈ G.activeIndices →
    G.machine.expectedLength (generatorData n) = (n : ℝ≥0∞)

def RawExpectedPolynomialTime (G : UniformGenerators α) : Prop :=
  ∃ p : PolynomialBound, ∀ n, n ∈ G.activeIndices →
    G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)

/-- Expected time on productive members, with one short run for every output. -/
def ExpectedPolynomialTime (G : UniformGenerators α) : Prop :=
  ∃ p : PolynomialBound,
    (∀ n, (G.layer n).Nonempty →
      G.machine.expectedRuntime (generatorData n) ≤ (p n : ℝ≥0∞)) ∧
    (∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p n) = .halted (.accepted word))

def PolynomialIndexCoverage (G : UniformGenerators α) : Prop :=
  ∃ q : PolynomialBound, ∀ word ∈ G.language,
    ∃ n, n ≤ q word.length ∧ word ∈ G.layer n

/-- The current paper's ELEPG efficiency condition is global: each word has
some producing index and an accepting path polynomial in the word length.
It imposes no bound on the other outputs or paths in that layer. -/
def GlobalWordPolynomialTime (G : UniformGenerators α) : Prop :=
  ∃ p : PolynomialBound, ∀ word ∈ G.language,
    ∃ n, ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (p word.length) = .halted (.accepted word)

/-- The older per-layer fast-path and index-coverage requirements imply the
paper's global condition. The converse is not assumed. -/
theorem globalWordPolynomialTime_of_layer_fast (G : UniformGenerators α)
    (expected : G.ExpectedPolynomialTime) (coverage : G.PolynomialIndexCoverage) :
    G.GlobalWordPolynomialTime := by
  obtain ⟨p,_,short⟩ := expected
  obtain ⟨q,coverage⟩ := coverage
  refine ⟨p.comp q,fun word member=>?_⟩
  obtain ⟨n,index,member⟩ := coverage word member
  obtain ⟨bits,nonempty,run⟩ := short n word member
  have growing : p n≤p (q word.length) :=
    Nat.mul_le_mul_left p.coefficient (pow_le_pow_left' (Nat.add_le_add_right index 1) p.degree)
  have limit : p n≤p.comp q word.length := growing.trans (p.comp_le q word.length)
  refine ⟨n,bits,nonempty,?_⟩
  simpa only [Nat.add_sub_of_le limit] using G.machine.run_halted_add (generatorData n) bits
    (p n) (.accepted word) run (p.comp q word.length-p n)

theorem ExpectedPolynomialTime.raw {G : UniformGenerators α}
    (expected : G.ExpectedPolynomialTime) : G.RawExpectedPolynomialTime := by
  obtain ⟨p, runtime, _⟩ := expected
  exact ⟨p, runtime⟩

/-- An infinite language cannot be covered by finitely many finite layers. -/
theorem activeIndices_infinite_of_finite_layers (G : UniformGenerators α)
    (infinite : G.language.Infinite) (finite : ∀ n, (G.layer n).Finite) :
    G.activeIndices.Infinite := by
  classical
  by_contra absent
  have indices : G.activeIndices.Finite := Set.not_infinite.mp absent
  have cover : G.language = ⋃ n ∈ G.activeIndices, G.layer n := by
    ext word
    constructor
    · rintro ⟨n, member⟩
      exact Set.mem_iUnion.mpr ⟨n, Set.mem_iUnion.mpr ⟨⟨word, member⟩, member⟩⟩
    · intro member
      obtain ⟨n, member⟩ := Set.mem_iUnion.mp member
      obtain ⟨_, member⟩ := Set.mem_iUnion.mp member
      exact ⟨n, member⟩
  exact infinite (cover ▸ indices.biUnion (fun n _ => finite n))

/-- The native fast-path condition bounds every output length in a fixed
layer, even when the layer's other executions have unbounded running times. -/
theorem layer_finite_of_short_paths (G : UniformGenerators α) (bound : ℕ → ℕ)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (bound n) = .halted (.accepted word))
    (n : ℕ) : (G.layer n).Finite := by
  apply (finite_words_length_le α (bound n)).subset
  intro word member
  obtain ⟨bits, _, accepted⟩ := short n word member
  exact G.machine.accepted_output_length_le (generatorData n) bits (bound n) word accepted

theorem activeIndices_infinite_of_short_paths (G : UniformGenerators α)
    (infinite : G.language.Infinite) (bound : ℕ → ℕ)
    (short : ∀ n word, word ∈ G.layer n → ∃ bits : BitString, bits ≠ [] ∧
      G.machine.run (generatorData n) bits (bound n) = .halted (.accepted word)) :
    G.activeIndices.Infinite :=
  G.activeIndices_infinite_of_finite_layers infinite (G.layer_finite_of_short_paths bound short)

/-- Thus the active-index infinitude clause follows from language infinitude
and the strengthened expected-time condition. -/
theorem ExpectedPolynomialTime.activeIndices_infinite {G : UniformGenerators α}
    (expected : G.ExpectedPolynomialTime) (infinite : G.language.Infinite) :
    G.activeIndices.Infinite := by
  obtain ⟨p, _, short⟩ := expected
  exact G.activeIndices_infinite_of_short_paths infinite p short

theorem ExpectedPolynomialTime.layer_finite {G : UniformGenerators α}
    (expected : G.ExpectedPolynomialTime) (n : ℕ) : (G.layer n).Finite := by
  obtain ⟨p, _, short⟩ := expected
  exact G.layer_finite_of_short_paths p short n

end UniformGenerators

/-- Expected polynomial-time exact generation, including finite languages. -/
def EPG (α : Type) [Fintype α] : LanguageClass α :=
  {L | ∃ G : GeneratorFamily α,
    G.toUniformGenerators.language = L ∧ G.toUniformGenerators.ExpectedPolynomialTime}

/-- The raw expected-length notion, without a global lucky-path requirement. -/
def ExpectedLengthExpectedPolynomialTime (α : Type) [Fintype α] : LanguageClass α :=
  {L | L.Infinite ∧ ∃ G : UniformGenerators α,
    G.language = L ∧ G.activeIndices.Infinite ∧
    G.ExpectedLength ∧ G.RawExpectedPolynomialTime}

/-- Stronger historical variant: every layer has short paths, with global
polynomial index coverage. This is not the current paper definition. -/
def LayerFastELEPG (α : Type) [Fintype α] : LanguageClass α :=
  {L | L.Infinite ∧ ∃ G : UniformGenerators α,
    G.language = L ∧ G.activeIndices.Infinite ∧
    G.ExpectedLength ∧ G.ExpectedPolynomialTime ∧ G.PolynomialIndexCoverage}

/-- Expected-length, expected-polynomial-time generation with the current
paper's word-length bound on at least one path for every word. -/
def ELEPG (α : Type) [Fintype α] : LanguageClass α :=
  {L | L.Infinite ∧ ∃ G : UniformGenerators α,
    G.language = L ∧ G.activeIndices.Infinite ∧
    G.ExpectedLength ∧ G.RawExpectedPolynomialTime ∧ G.GlobalWordPolynomialTime}

/-- The productive-index infinitude field follows from the other layer-fast
hypotheses and need not be supplied separately by a construction. -/
theorem mem_layerFastELEPG_of_expected_family {α : Type} [Fintype α] {L : Language α}
    (infinite : L.Infinite) (G : UniformGenerators α) (language : G.language = L)
    (mean : G.ExpectedLength) (expected : G.ExpectedPolynomialTime)
    (coverage : G.PolynomialIndexCoverage) : L ∈ LayerFastELEPG α := by
  refine ⟨infinite, G, language, expected.activeIndices_infinite ?_, mean, expected, coverage⟩
  rwa [language]

/-- Every stronger layer-fast family is a witness for the paper class. -/
theorem layerFastELEPG_subset_elepg {α : Type} [Fintype α] : LayerFastELEPG α ⊆ ELEPG α := by
  rintro L ⟨infinite,G,language,active,mean,expected,coverage⟩
  exact ⟨infinite,G,language,active,mean,expected.raw,
    G.globalWordPolynomialTime_of_layer_fast expected coverage⟩

/-- Package a paper-ELEPG family without adding a per-layer fast-path premise. -/
theorem mem_elepg_of_raw_expected_family {α : Type} [Fintype α] {L : Language α}
    (infinite : L.Infinite) (G : UniformGenerators α) (language : G.language=L)
    (active : G.activeIndices.Infinite) (mean : G.ExpectedLength)
    (expected : G.RawExpectedPolynomialTime) (fast : G.GlobalWordPolynomialTime) : L∈ELEPG α :=
  ⟨infinite,G,language,active,mean,expected,fast⟩

namespace GeneratorFamily

variable {α : Type} [Fintype α] (G : GeneratorFamily α)

/-- Exact output length gives the same mean at every productive index. -/
theorem expectedLength : G.toUniformGenerators.ExpectedLength := by
  intro n nonempty
  have productive := (G.machine.generator_probability_one_iff_nonempty
    (generatorData n) (G.isGenerator n)).mpr nonempty
  have accepted : ∀ᵐ stream ∂fairCoinMeasure,
      stream ∈ G.machine.acceptedStreams (generatorData n) := by
    apply (ae_mem_iff_measure_eq
      (G.machine.measurableSet_acceptedStreams (generatorData n)).nullMeasurableSet).mpr
    simpa using productive
  have lengths : ∀ᵐ stream ∂fairCoinMeasure,
      (G.machine.streamLength (generatorData n) stream : ℝ≥0∞) = (n : ℝ≥0∞) := by
    filter_upwards [accepted] with stream member
    obtain ⟨bits, cylinderMember, word, produces⟩ := member
    have generated : word ∈ G.toUniformGenerators.layer n :=
      ⟨bits ++ [false], by simp,
        G.machine.produces_append (generatorData n) bits [false] word produces⟩
    rw [G.machine.streamLength_of_produces (generatorData n)
      ⟨bits, cylinderMember, produces⟩, G.outputLength n word generated]
  rw [Machine.expectedLength, lintegral_congr_ae lengths]
  simp

/-- Compatibility name: the all-slices premise is no longer needed. -/
theorem expectedLength_of_nonempty_layers
    (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time)
    (nonempty : ∀ n, (G.toUniformGenerators.layer n).Nonempty) :
    G.toUniformGenerators.ExpectedLength := G.expectedLength

/-- Over a finite alphabet, an infinite exact language has infinitely many
productive length slices. -/
theorem activeIndices_infinite (infinite : G.toUniformGenerators.language.Infinite) :
    G.toUniformGenerators.activeIndices.Infinite := by
  apply G.toUniformGenerators.activeIndices_infinite_of_finite_layers infinite
  intro n
  exact (finite_words_length_eq α n).subset (fun word member => G.outputLength n word member)

theorem polynomialIndexCoverage : G.toUniformGenerators.PolynomialIndexCoverage := by
  refine ⟨⟨1, 1, by decide⟩, ?_⟩
  rintro word ⟨n, member⟩
  refine ⟨n, ?_, member⟩
  simp only [PolynomialBound.eval, one_mul, pow_one]
  have length := G.outputLength n word member
  omega

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

theorem pg_subset_epg {α : Type} [Fintype α] : PG α ⊆ EPG α := by
  rintro L ⟨G, language, seed, time, bounded⟩
  exact ⟨G, language, G.expectedPolynomialTime_of_polynomialTime seed time bounded⟩

/-- The first inclusion is stated only for infinite languages, as in the paper. -/
theorem epg_mem_layerFastELEPG_of_infinite {α : Type} [Fintype α] {L : Language α}
    (expected : L ∈ EPG α) (infinite : L.Infinite) : L ∈ LayerFastELEPG α := by
  obtain ⟨G, language, expected⟩ := expected
  refine ⟨infinite, G.toUniformGenerators, language, ?_, G.expectedLength,
    expected, G.polynomialIndexCoverage⟩
  apply G.activeIndices_infinite
  rwa [language]

theorem pg_mem_layerFastELEPG_of_infinite {α : Type} [Fintype α] {L : Language α}
    (pg : L ∈ PG α) (infinite : L.Infinite) : L ∈ LayerFastELEPG α :=
  epg_mem_layerFastELEPG_of_infinite (pg_subset_epg pg) infinite

/-- Compatibility with the previous public conversion; now a special case. -/
theorem pg_mem_layerFastELEPG_of_nonempty_slices {α : Type} [Fintype α] {L : Language α}
    (pg : L ∈ PG α) (slices : ∀ n, (lengthSlice L n).Nonempty) : L ∈ LayerFastELEPG α :=
  pg_mem_layerFastELEPG_of_infinite pg (language_infinite_of_nonempty_slices L slices)

/-- The first inclusion in Theorem 5.1, for infinite languages. -/
theorem epg_mem_elepg_of_infinite {α : Type} [Fintype α] {L : Language α}
    (expected : L ∈ EPG α) (infinite : L.Infinite) : L ∈ ELEPG α :=
  layerFastELEPG_subset_elepg (epg_mem_layerFastELEPG_of_infinite expected infinite)

theorem pg_mem_elepg_of_infinite {α : Type} [Fintype α] {L : Language α}
    (pg : L ∈ PG α) (infinite : L.Infinite) : L ∈ ELEPG α :=
  epg_mem_elepg_of_infinite (pg_subset_epg pg) infinite

theorem pg_mem_elepg_of_nonempty_slices {α : Type} [Fintype α] {L : Language α}
    (pg : L ∈ PG α) (slices : ∀ n,(lengthSlice L n).Nonempty) : L ∈ ELEPG α :=
  pg_mem_elepg_of_infinite pg (language_infinite_of_nonempty_slices L slices)

theorem elepg_subset_expectedLengthExpectedPolynomialTime {α : Type} [Fintype α] :
    ELEPG α ⊆ ExpectedLengthExpectedPolynomialTime α := by
  rintro L ⟨infinite, G, language, active, mean, expected, _⟩
  exact ⟨infinite, G, language, active, mean, expected⟩

end ComplexityOfGenerators
