import ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex.Prepare
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness
import ComplexityOfGenerators.MultitapeModel

/-! Ordinary-input interface for a genuine length-indexed finite bank.
The charged cost includes writing/rewinding the actual unary index and every
source lookup/inspect/commit transition. This is a linear-time simulation;
it does not use the quadratic single-work-tape compiler. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} (M : MultitapeMachine I A O)

def machine : MultitapeMachine I A O where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := M.outputFinite
  Control := Phase M.Control M.Work M.tapes
  Work := Cell (S := M.Work)
  controlFinite := inferInstance
  workFinite := inferInstance
  tapes := M.tapes + 1
  program := bank M.program

/-- Complete simulation from the actual blank-bank initial configuration. -/
theorem initial_executes (data : InputData I A) (bits : BitString)
    (ticks : ℕ) (result : Outcome O)
    (source : M.Executes (sourceData data) bits M.initialConfiguration ticks result) :
    ∃ targetTicks, targetTicks ≤ 2 * data.input.length + 3 * ticks + 3 ∧
      (machine M).Executes data bits (machine M).initialConfiguration targetTicks result := by
  obtain ⟨remaining, cost, execution⟩ := executes M.program data bits source 0
    (M.program.initial_bounded (sourceData data))
  have prepared := prepare_path M.program data bits
  refine ⟨2 * data.input.length + 2 + remaining, by omega, ?_⟩
  change (bank M.program).Executes data bits (bank M.program).initialConfiguration
    (2 * data.input.length + 2 + remaining) result
  exact prepared.executes (bank M.program) execution

theorem terminates (data : InputData I A) (source : M.Terminates (sourceData data)) :
    (machine M).Terminates data := by
  intro bits
  obtain ⟨ticks, result, execution⟩ := source bits
  obtain ⟨targetTicks, _, simulated⟩ := initial_executes M data bits ticks result execution
  exact ⟨targetTicks, result, simulated⟩

/-- The only additional asymptotic cost is the actual O(n) index preparation. -/
theorem timeBound (data : InputData I A) (time : ℕ)
    (source : M.TimeBound (sourceData data) time) :
    (machine M).TimeBound data (2 * data.input.length + 3 * time + 3) := by
  intro bits
  obtain ⟨ticks, result, cost, execution⟩ := source bits
  obtain ⟨targetTicks, compiledCost, simulated⟩ := initial_executes M data bits ticks result execution
  exact ⟨targetTicks, result, by omega, simulated⟩

theorem produces_iff (data : InputData I A) (bits : BitString)
    (source : M.Terminates (sourceData data)) (word : Word O) :
    (machine M).Produces data bits word ↔ M.Produces (sourceData data) bits word := by
  constructor
  · rintro ⟨targetTicks, accepted⟩
    obtain ⟨ticks, result, execution⟩ := source bits
    obtain ⟨otherTicks, _, simulated⟩ := initial_executes M data bits ticks result execution
    have same := (TapeBank.Executes.unique (bank M.program) accepted simulated).2
    subst result
    exact ⟨ticks, execution⟩
  · rintro ⟨ticks, execution⟩
    obtain ⟨targetTicks, _, simulated⟩ := initial_executes M data bits ticks (.accepted word) execution
    exact ⟨targetTicks, simulated⟩

theorem accepts_iff (data : InputData I A) (bits : BitString)
    (source : M.Terminates (sourceData data)) :
    (machine M).Accepts data bits ↔ M.Accepts (sourceData data) bits :=
  exists_congr fun word => produces_iff M data bits source word

theorem acceptingTimeBound (data : InputData I A)
    (source : M.Terminates (sourceData data)) (time : ℕ)
    (bounded : M.AcceptingTimeBound (sourceData data) time) :
    (machine M).AcceptingTimeBound data (2 * data.input.length + 3 * time + 3) := by
  intro bits targetTicks word accepted
  obtain ⟨ticks, execution⟩ := (produces_iff M data bits source word).mp ⟨targetTicks, accepted⟩
  obtain ⟨otherTicks, cost, simulated⟩ := initial_executes M data bits ticks (.accepted word) execution
  have same := (TapeBank.Executes.unique (bank M.program) accepted simulated).1
  have sourceCost := bounded bits ticks word execution
  omega

end
end ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex
