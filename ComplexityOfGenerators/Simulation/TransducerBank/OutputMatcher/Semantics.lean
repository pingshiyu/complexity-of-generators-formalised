import ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher.Execution
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness
import ComplexityOfGenerators.MultitapeModel

namespace ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (M : MultitapeMachine Unit Bool α)

/-- A finite streaming matcher for a general finite work-tape bank. -/
def machine : MultitapeMachine α Bool Unit where
  inputFinite := M.outputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := inferInstance
  Control := M.Control × Bool
  Work := M.Work
  controlFinite := inferInstance
  workFinite := inferInstance
  tapes := M.tapes
  program := bank M.program

theorem initial_executes (data : InputData α Bool) (bits : BitString)
    (ticks : ℕ) (result : Outcome α)
    (execution : M.Executes (sourceData data) bits M.initialConfiguration ticks result) :
    (machine M).Executes data bits (machine M).initialConfiguration ticks (outcome data.input result) := by
  change (bank M.program).Executes data bits (bank M.program).initialConfiguration ticks
    (outcome data.input result)
  simpa only [configuration_initial] using executes M.program data bits execution

theorem terminates (data : InputData α Bool) (source : M.Terminates (sourceData data)) :
    (machine M).Terminates data := by
  intro bits
  obtain ⟨ticks, result, execution⟩ := source bits
  exact ⟨ticks, outcome data.input result, initial_executes M data bits ticks result execution⟩

theorem timeBound (data : InputData α Bool) (time : ℕ)
    (source : M.TimeBound (sourceData data) time) : (machine M).TimeBound data time := by
  intro bits
  obtain ⟨ticks, result, cost, execution⟩ := source bits
  exact ⟨ticks, outcome data.input result, cost, initial_executes M data bits ticks result execution⟩

/-- The supplied index is unchanged. Removing that supplied unary index is a
separate ordinary-input preparation step and is not hidden in this theorem. -/
theorem accepts_word_iff (data : InputData α Bool) (bits : BitString)
    (source : M.Terminates (sourceData data)) :
    (machine M).Accepts data bits ↔ M.Produces (sourceData data) bits data.input := by
  constructor
  · rintro ⟨targetWord, targetTicks, accepted⟩
    obtain ⟨sourceTicks, result, execution⟩ := source bits
    have simulated := initial_executes M data bits sourceTicks result execution
    have same := (TapeBank.Executes.unique (bank M.program) accepted simulated).2
    cases result with
    | rejected => cases same
    | exhausted => cases same
    | accepted emitted =>
      have equal : emitted = data.input := by
        by_contra different
        simp [outcome, different] at same
      subst emitted
      exact ⟨sourceTicks, execution⟩
  · rintro ⟨ticks, execution⟩
    refine ⟨[], ticks, ?_⟩
    simpa [outcome] using
      initial_executes M data bits ticks (.accepted data.input) execution

/-- Both successful-run time and the exact primitive clock are preserved. -/
theorem acceptingTimeBound (data : InputData α Bool)
    (source : M.Terminates (sourceData data)) (time : ℕ)
    (bounded : M.AcceptingTimeBound (sourceData data) time) :
    (machine M).AcceptingTimeBound data time := by
  intro bits targetTicks targetWord accepted
  obtain ⟨sourceTicks, execution⟩ :=
    (accepts_word_iff M data bits source).mp ⟨targetWord, targetTicks, accepted⟩
  have simulated : (machine M).Executes data bits (machine M).initialConfiguration
      sourceTicks (.accepted []) := by
    simpa [outcome] using
      initial_executes M data bits sourceTicks (.accepted data.input) execution
  have same := (TapeBank.Executes.unique (bank M.program) accepted simulated).1
  exact same ▸ bounded bits sourceTicks data.input execution

end
end ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher
