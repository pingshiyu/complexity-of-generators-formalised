import ComplexityOfGenerators.Proofs.GeneratorSupport
import ComplexityOfGenerators.ComplexityClasses

/-!
# Reusable criteria for constructing polynomial generators

The machine-specific work is to prove termination, absence of explicit rejection,
acceptance on full trials, and the generated length slices. These lemmas handle
the common probability argument and packaging into the paper's `PG` class.
Neither criterion assumes a compiler or changes the generator definitions.
-/

namespace ComplexityOfGenerators

namespace Machine

variable {I A O : Type} (M : Machine I A O) (data : InputData I A)

/-- Full trials of one fixed length suffice for the zero-or-one productivity
condition. A nonempty language accepts a prefix of every infinite stream; an
empty language has no accepted streams. The seed length may be zero. -/
theorem isGenerator_of_full_trials (seed : ℕ)
    (halting : M.HaltingTransducer data)
    (fullTrial : ∀ bits : BitString, bits.length = seed →
      (M.Accepts data bits ↔ (M.generatedLanguage data).Nonempty)) :
    M.IsGenerator data := by
  classical
  refine ⟨halting, ?_⟩
  by_cases nonempty : (M.generatedLanguage data).Nonempty
  · left
    have acceptsEveryStream : M.acceptedStreams data = Set.univ := by
      apply Set.eq_univ_of_forall
      intro stream
      exact ⟨streamPrefix stream seed, stream_mem_prefix_cylinder _ _,
        (fullTrial _ (by simp)).mpr nonempty⟩
    rw [acceptsEveryStream]
    exact MeasureTheory.measure_univ
  · right
    have emptyLanguage := Set.not_nonempty_iff_eq_empty.mp nonempty
    rw [(M.acceptedStreams_eq_empty_iff data).mpr emptyLanguage]
    exact MeasureTheory.measure_empty

end Machine

/-- Package a single native machine as a polynomial generator once its size-`n`
support is exactly the length-`n` slice of `L`. Exact output length and the union
of all slices follow from that equality, including the empty-word slice. -/
theorem mem_pg_of_lengthSlices {α : Type} [Fintype α] (L : Language α)
    (M : Machine Unit Bool α) (seed time : PolynomialBound)
    (generator : ∀ n, M.IsGenerator (generatorData n))
    (slices : ∀ n, M.generatedLanguage (generatorData n) = lengthSlice L n)
    (bounded : ∀ n, M.GeneratorTimeBound (generatorData n) (seed n) (time n)) :
    L ∈ PG α := by
  let G : GeneratorFamily α := {
    machine := M
    isGenerator := generator
    outputLength := by
      intro n word member
      change word ∈ M.generatedLanguage (generatorData n) at member
      rw [slices n] at member
      exact member.2 }
  refine ⟨G, ?_, seed, time, bounded⟩
  ext word
  change (∃ n, word ∈ M.generatedLanguage (generatorData n)) ↔ word ∈ L
  simp only [slices]
  exact ⟨fun ⟨_, member, _⟩ => member, fun member => ⟨word.length, member, rfl⟩⟩

end ComplexityOfGenerators
