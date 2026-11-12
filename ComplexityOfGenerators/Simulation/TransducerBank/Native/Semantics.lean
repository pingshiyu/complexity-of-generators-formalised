import ComplexityOfGenerators.Simulation.TransducerBank.Native.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness

namespace ComplexityOfGenerators.Simulation.TransducerBank.Native

variable {I A O : Type} (M : Machine I A O)

/-- This is an exact transition-preserving embedding, not the quadratic compiler. -/
theorem terminates (data : InputData I A) (halts : ∀ bits, M.Halts data bits) :
    (machine M).Terminates data := by
  intro bits
  obtain ⟨ticks, result, run⟩ := halts bits
  rw [← M.runFrom_initial] at run
  obtain ⟨bankTicks, _, execution⟩ :=
    executes_of_run M data bits M.initialConfiguration ticks result run
  exact ⟨bankTicks, result, execution⟩

theorem produces_iff (data : InputData I A) (halts : ∀ bits, M.Halts data bits)
    (bits : BitString) (word : Word O) :
    (machine M).Produces data bits word ↔ M.Produces data bits word := by
  constructor
  · rintro ⟨bankTicks, execution⟩
    obtain ⟨ticks, result, run⟩ := halts bits
    have initialRun := run
    rw [← M.runFrom_initial] at run
    obtain ⟨otherTicks, _, otherExecution⟩ :=
      executes_of_run M data bits M.initialConfiguration ticks result run
    have same := (TapeBank.Executes.unique (bank M) execution otherExecution).2
    subst result
    exact ⟨ticks, initialRun⟩
  · rintro ⟨ticks, run⟩
    rw [← M.runFrom_initial] at run
    obtain ⟨bankTicks, _, execution⟩ :=
      executes_of_run M data bits M.initialConfiguration ticks (.accepted word) run
    exact ⟨bankTicks, execution⟩

theorem accepts_iff (data : InputData I A) (halts : ∀ bits, M.Halts data bits)
    (bits : BitString) :
    (machine M).Accepts data bits ↔ M.Accepts data bits :=
  exists_congr fun word => produces_iff M data halts bits word

theorem generatedLanguage (data : InputData I A) (halts : ∀ bits, M.Halts data bits) :
    (machine M).generatedLanguage data = M.generatedLanguage data := by
  ext word
  exact exists_congr fun bits => and_congr_right fun _ =>
    produces_iff M data halts bits word

theorem acceptedStreams (data : InputData I A) (halts : ∀ bits, M.Halts data bits) :
    (machine M).acceptedStreams data = M.acceptedStreams data := by
  ext stream
  exact exists_congr fun bits => and_congr_right fun _ =>
    accepts_iff M data halts bits

theorem isGenerator (data : InputData I A) (generator : M.IsGenerator data) :
    (machine M).IsGenerator data := by
  refine ⟨⟨terminates M data generator.1.1, ?_⟩, ?_⟩
  · intro bits bankTicks execution
    obtain ⟨ticks, result, run⟩ := generator.1.1 bits
    have initialRun := run
    rw [← M.runFrom_initial] at run
    obtain ⟨otherTicks, _, otherExecution⟩ :=
      executes_of_run M data bits M.initialConfiguration ticks result run
    have same := (TapeBank.Executes.unique (bank M) execution otherExecution).2
    subst result
    exact generator.1.2 bits ticks initialRun
  · rw [acceptedStreams M data generator.1.1]
    exact generator.2

theorem acceptingTimeBound (data : InputData I A) (halts : ∀ bits, M.Halts data bits)
    (time : ℕ)
    (bounded : ∀ bits word, M.Produces data bits word →
      M.run data bits time = .halted (.accepted word)) :
    (machine M).AcceptingTimeBound data time := by
  intro bits bankTicks word execution
  have produces : M.Produces data bits word :=
    (produces_iff M data halts bits word).mp ⟨bankTicks, execution⟩
  have run := bounded bits word produces
  rw [← M.runFrom_initial] at run
  obtain ⟨ticks, small, other⟩ :=
    executes_of_run M data bits M.initialConfiguration time (.accepted word) run
  have same := (TapeBank.Executes.unique (bank M) execution other).1
  exact same ▸ small

end ComplexityOfGenerators.Simulation.TransducerBank.Native
