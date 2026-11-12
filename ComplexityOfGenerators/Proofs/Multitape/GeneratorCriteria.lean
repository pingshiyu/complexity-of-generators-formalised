import ComplexityOfGenerators.Simulation.TransducerBank.AcceptedRandomTape
import ComplexityOfGenerators.Simulation.TransducerBank.Embedding
import ComplexityOfGenerators.Foundations.StreamPrefixExecution
import ComplexityOfGenerators.Foundations.Probability

namespace ComplexityOfGenerators.MultitapeMachine

open Simulation.TransducerBank

variable {I A O : Type} (M : MultitapeMachine I A O)

/-- A uniformly bounded bank with no explicit rejection accepts every infinite
choice stream. The proof charges real transitions and uses the consumed-bit
bound, rather than assuming a trial-success interface. -/
theorem isGenerator_of_timeBound (data : InputData I A) (time : ℕ)
    (bounded : M.TimeBound data time)
    (noRejected : ∀ bits ticks, ¬ M.Executes data bits M.initialConfiguration ticks .rejected) :
    M.IsGenerator data := by
  classical
  have fullAccepts : ∀ bits : BitString, bits.length = time + 1 → M.Accepts data bits := by
    intro bits length
    obtain ⟨ticks, result, cost, execution⟩ := bounded bits
    cases result with
    | accepted word => exact ⟨word, ticks, execution⟩
    | rejected => exact False.elim (noRejected bits ticks execution)
    | exhausted =>
      obtain ⟨finish, no, yes, path, _, absent⟩ :=
        TapeBank.Executes.exhausted_path M.program execution rfl
      have consumed := path.random_growth M.program
      have ended := List.getElem?_eq_none_iff.mp absent
      change finish.randomHead ≤ 0 + ticks at consumed
      omega
  have allStreams : M.acceptedStreams data = Set.univ := by
    apply Set.eq_univ_of_forall
    intro stream
    exact ⟨streamPrefix stream (time + 1), stream_mem_prefix_cylinder _ _,
      fullAccepts _ (by simp)⟩
  refine ⟨⟨?_, noRejected⟩, Or.inl ?_⟩
  · intro bits
    obtain ⟨ticks, result, _, execution⟩ := bounded bits
    exact ⟨ticks, result, execution⟩
  · rw [allStreams]
    exact MeasureTheory.measure_univ

/-- Empty finite generators still need finite-tape termination and no explicit
rejection, but impose no common time bound on their draining executions. -/
theorem isGenerator_of_empty (data : InputData I A)
    (halting : M.HaltingTransducer data)
    (noAccepts : ∀ bits, ¬ M.Accepts data bits) : M.IsGenerator data := by
  have noStreams : M.acceptedStreams data = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    rintro stream ⟨bits, _, accepted⟩
    exact noAccepts bits accepted
  refine ⟨halting, Or.inr ?_⟩
  rw [noStreams]
  exact MeasureTheory.measure_empty

end ComplexityOfGenerators.MultitapeMachine
