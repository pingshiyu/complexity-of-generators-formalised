import ComplexityOfGenerators.Foundations.StreamSemantics

/-!
# Finite simulation of accepting stream executions

A run of `time` native transitions can inspect at most `time + 1` random
cells.  Consequently, accepting stream executions can be recovered by running
the machine on this fixed-length prefix.  The result needs no worst-case
runtime hypothesis and applies to expected-time generators.
-/

namespace ComplexityOfGenerators

namespace Machine

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

/-- A stream prefix longer than the clock reproduces every non-exhausted run
on any other prefix of the same stream. -/
theorem run_streamPrefix_eq_of_not_exhausted
    {stream : BitStream} {bits : BitString} {time size : ℕ}
    (member : stream ∈ cylinder bits) (long : time < size)
    (live : M.run data bits time ≠ .halted .exhausted) :
    M.run data (streamPrefix stream size) time = M.run data bits time := by
  by_cases short : bits.length ≤ size
  · have initial : bits <+: streamPrefix stream size :=
      cylinder_prefix_comparable member (stream_mem_prefix_cylinder stream size)
        (by simpa using short)
    obtain ⟨tail, equal⟩ := initial
    simpa only [equal] using M.run_append_of_not_exhausted data bits tail time live
  · have initial : streamPrefix stream size <+: bits :=
      cylinder_prefix_comparable (stream_mem_prefix_cylinder stream size) member
        (by simp; omega)
    obtain ⟨tail, equal⟩ := initial
    have notExhausted :
        M.run data (streamPrefix stream size) time ≠ .halted .exhausted :=
      M.run_not_exhausted_of_length data (streamPrefix stream size) time (by simpa using long)
    have extended := M.run_append_of_not_exhausted data (streamPrefix stream size) tail time notExhausted
    simpa only [equal] using extended.symm

theorem run_on_streamPrefix_of_accepting_prefix
    {stream : BitStream} {bits : BitString} {word : List O} {time : ℕ}
    (member : stream ∈ cylinder bits)
    (accepted : M.run data bits time = .halted (.accepted word)) :
    M.run data (streamPrefix stream (time + 1)) time = .halted (.accepted word) := by
  rw [M.run_streamPrefix_eq_of_not_exhausted data member (by omega) (by simp [accepted]), accepted]

/-- The finite prefix has a uniform size determined solely by the simulation
clock, even if the original accepting seed was arbitrarily long. -/
theorem streamAcceptsBy_run_streamPrefix
    {stream : BitStream} {time : ℕ}
    (accepted : M.streamAcceptsBy data stream time) :
    ∃ word, M.run data (streamPrefix stream (time + 1)) time = .halted (.accepted word) := by
  obtain ⟨bits, word, member, run⟩ := accepted
  exact ⟨word, M.run_on_streamPrefix_of_accepting_prefix data member run⟩

theorem streamProduces_run_streamPrefix
    {stream : BitStream} {word : List O} {time : ℕ}
    (produces : M.streamProduces data stream word)
    (accepted : M.streamAcceptsBy data stream time) :
    M.run data (streamPrefix stream (time + 1)) time = .halted (.accepted word) := by
  obtain ⟨output, run⟩ := M.streamAcceptsBy_run_streamPrefix data accepted
  have same : output = word := M.streamProduces_unique data
    ⟨streamPrefix stream (time + 1), stream_mem_prefix_cylinder stream (time + 1), time, run⟩ produces
  simpa only [same] using run

/-- The expectation-based clock bound has the same finite-prefix operational
consequence as a direct stream-acceptance bound. -/
theorem streamProduces_run_streamPrefix_of_runtime_le
    {stream : BitStream} {word : List O} {time : ℕ}
    (produces : M.streamProduces data stream word)
    (runtime : M.streamRuntime data stream ≤ time) :
    M.run data (streamPrefix stream (time + 1)) time = .halted (.accepted word) :=
  M.streamProduces_run_streamPrefix data produces (M.acceptsBy_of_streamRuntime_le data runtime)

/-- A bounded-runtime event can be tested using one fixed finite random tape,
and the finite result retains the stream random variable's output length. -/
theorem streamLength_run_streamPrefix_of_runtime_le
    {stream : BitStream} {time : ℕ}
    (runtime : M.streamRuntime data stream ≤ time) :
    ∃ word, M.run data (streamPrefix stream (time + 1)) time = .halted (.accepted word) ∧
      word.length = M.streamLength data stream := by
  obtain ⟨word, run⟩ := M.streamAcceptsBy_run_streamPrefix data
    (M.acceptsBy_of_streamRuntime_le data runtime)
  refine ⟨word, run, ?_⟩
  exact (M.streamLength_of_produces data
    ⟨streamPrefix stream (time + 1), stream_mem_prefix_cylinder stream (time + 1), time, run⟩).symm

end Machine

end ComplexityOfGenerators
