import ComplexityOfGenerators.Foundations.StreamSemantics

/-!
# Boundary cases and operational meaning of stream random variables

These facts identify the zero length assigned to an unproductive stream, its
infinite acceptance time, and the exact number of native transitions before a
first acceptance.  Positive output-length expectation therefore supplies a
nonempty layer without any additional productivity hypothesis.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

namespace Machine

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

theorem not_streamAcceptsBy_of_not_accepted
    {stream : BitStream} (absent : stream ∉ M.acceptedStreams data) (time : ℕ) :
    ¬ M.streamAcceptsBy data stream time := by
  rintro ⟨bits, word, member, run⟩
  exact absent ⟨bits, member, word, time, run⟩

theorem streamLength_eq_zero_of_not_accepted
    {stream : BitStream} (absent : stream ∉ M.acceptedStreams data) :
    M.streamLength data stream = 0 := by
  rcases M.streamLength_spec data stream with length | ⟨zero, _⟩
  · obtain ⟨word, ⟨bits, member, produces⟩, _⟩ := length
    exact False.elim (absent ⟨bits, member, word, produces⟩)
  · exact zero

theorem streamRuntime_eq_top_of_not_accepted
    {stream : BitStream} (absent : stream ∉ M.acceptedStreams data) :
    M.streamRuntime data stream = ∞ := by
  classical
  have never := M.not_streamAcceptsBy_of_not_accepted data absent
  simp only [streamRuntime, ite_eq_right (never _)]
  exact ENNReal.tsum_const_eq_top_of_ne_zero one_ne_zero

/-- In the native evaluator terminal observations cost no transition.  If the
first accepting observation is at clock `time`, the runtime is exactly `time`. -/
theorem streamRuntime_eq_of_first_acceptsBy
    {stream : BitStream} {time : ℕ}
    (accepted : M.streamAcceptsBy data stream time)
    (earlier : ∀ t < time, ¬ M.streamAcceptsBy data stream t) :
    M.streamRuntime data stream = time := by
  classical
  apply le_antisymm (M.streamRuntime_le_of_acceptsBy data accepted)
  calc
    (time : ℝ≥0∞) = ∑ t ∈ Finset.range time, (1 : ℝ≥0∞) := by simp
    _ = ∑ t ∈ Finset.range time,
        (if M.streamAcceptsBy data stream t then (0 : ℝ≥0∞) else 1) := by
          apply Finset.sum_congr rfl
          intro t ht
          simp [earlier t (Finset.mem_range.mp ht)]
    _ ≤ M.streamRuntime data stream :=
      ENNReal.sum_le_tsum (Finset.range time)

/-- Empty accepted seeds cause no exception: append one unused bit to obtain
the nonempty finite witness used by `generatedLanguage`. -/
theorem streamProduces_mem_generatedLanguage
    {stream : BitStream} {word : List O}
    (produces : M.streamProduces data stream word) :
    word ∈ M.generatedLanguage data := by
  obtain ⟨bits, _, produces⟩ := produces
  exact ⟨bits ++ [false], by simp, M.produces_append data bits [false] word produces⟩

theorem streamLength_pos_mem_generatedLanguage
    {stream : BitStream} (positive : 0 < M.streamLength data stream) :
    ∃ word, word ∈ M.generatedLanguage data ∧
      M.streamProduces data stream word ∧ word.length = M.streamLength data stream := by
  rcases M.streamLength_spec data stream with length | ⟨zero, _⟩
  · obtain ⟨word, produces, length⟩ := length
    exact ⟨word, M.streamProduces_mem_generatedLanguage data produces, produces, length⟩
  · omega

theorem expectedLength_eq_zero_of_generatedLanguage_empty
    (empty : M.generatedLanguage data = ∅) : M.expectedLength data = 0 := by
  have noStreams := (M.acceptedStreams_eq_empty_iff data).mpr empty
  have zero (stream : BitStream) : M.streamLength data stream = 0 :=
    M.streamLength_eq_zero_of_not_accepted data (by simp [noStreams])
  simp [expectedLength, zero]

/-- This supplies the nonempty-layer premise in expected polynomial runtime
bounds at every positive expected-length index. -/
theorem generatedLanguage_nonempty_of_expectedLength_pos
    (positive : 0 < M.expectedLength data) : (M.generatedLanguage data).Nonempty := by
  by_contra absent
  have empty := Set.not_nonempty_iff_eq_empty.mp absent
  have zero := M.expectedLength_eq_zero_of_generatedLanguage_empty data empty
  simp [zero] at positive

end Machine

end ComplexityOfGenerators
