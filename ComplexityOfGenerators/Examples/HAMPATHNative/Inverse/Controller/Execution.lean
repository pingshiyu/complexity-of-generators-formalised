import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Dispatch

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

noncomputable def commandBudget (n : ℕ) (target label : List Symbol) (bits : BitString) : ℕ :=
  3*n+input.cost (indexed n target label).store+
    Classify.routine.cost (preparedStore n target label)+dispatchBudget bits (classified n target label)+4

theorem command_runs (graph : Graph) (start n : ℕ) (label : List Symbol) (bits : BitString)
    (inside : start<graph.size) :
    ∃ ticks≤commandBudget n (graph.encode start) label bits, ∃ result,
      command.Runs n bits (loaded (graph.encode start) label) ticks result ∧
        result.outcome=valueOutcome (value graph start n label bits) := by
  let target := graph.encode start
  have loadRun := Command.loadIndex_runs (O := Symbol) (34 : Fin 64) (Symbol.bit true) n bits
    (loaded target label) (Nat.zero_le _)
  obtain ⟨inputTicks,inputCost,inputRun⟩ := input.runs (n := n) bits (indexed n target label) le_rfl
  have ready : {indexed n target label with store := input.eval (indexed n target label).store}=
      prepared n target label := by
    rw [input_value]
    rfl
  rw [ready] at inputRun
  obtain ⟨classifyTicks,classifyCost,classifyRun⟩ := Classify.routine.runs (n := n) bits (prepared n target label) le_rfl
  change Classify.routine.command.Runs n bits (prepared n target label) classifyTicks (.done (classified n target label)) at classifyRun
  have properties := classified_graph graph start n label inside
  obtain ⟨lastTicks,lastCost,result,lastRun,outcome⟩ := dispatch_runs bits (classified n target label) le_rfl
    graph start label inside properties rfl rfl
  have run := Command.Runs.seq _ _ _ _ _ _ _ loadRun
    (Command.Runs.seq _ _ _ _ _ _ _ inputRun (Command.Runs.seq _ _ _ _ _ _ _ classifyRun lastRun))
  refine ⟨3*n+1+(inputTicks+1+(classifyTicks+1+lastTicks)),?_,result,run,outcome⟩
  change _≤commandBudget n target label bits
  unfold commandBudget
  change inputTicks ≤ input.cost (indexed n target label).store at inputCost
  change classifyTicks≤Classify.routine.cost (preparedStore n target label) at classifyCost
  omega

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
