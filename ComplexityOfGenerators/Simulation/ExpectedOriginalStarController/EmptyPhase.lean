import ComplexityOfGenerators.Simulation.ExpectedStarGenerator.PathTotal
import ComplexityOfGenerators.Simulation.WordStack.OutputMapping

/-! The existing certified-path controller has an unused alphabet summand
parameterised by a bounded phase family. A concrete empty family discharges
that parameter without imposing any bound on the original source family. -/
namespace ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
noncomputable section
variable {α : Type} [Fintype α]

def emptyMachine : Machine Unit Bool α where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 1
  symbols := 0
  initial := 0
  transition := fun _ _ _ _ _ => .reject

theorem emptyMachine_run (data : InputData Unit Bool) (bits : BitString) (time : ℕ) :
    (emptyMachine (α := α)).run data bits time = .halted .rejected := by
  induction time with
  | zero => rfl
  | succ time ih => simp only [Machine.run,ih]

noncomputable def emptyPhase : BoundedPhaseFamily α where
  machine := emptyMachine
  seed := ⟨1,0,by decide⟩
  clock := ⟨1,0,by decide⟩
  reciprocal := ⟨1,0,by decide⟩
  mean := by
    intro n
    simp [OptionPhase.HasMean,OptionPhase.success,UnionGenerator.sourceValue,emptyMachine_run,
      RunState.acceptedWord,Outcome.acceptedWord,BalancedPairPhase.optionLength]
  mass := by
    intro n active
    rcases active with ⟨bits,word,output⟩
    simp [UnionGenerator.sourceValue,emptyMachine_run,RunState.acceptedWord,Outcome.acceptedWord] at output

end
end ComplexityOfGenerators.Simulation.ExpectedOriginalStarController
