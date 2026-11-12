import ComplexityOfGenerators.Simulation.OriginalHeaderController.Phase

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool)

theorem boot_runs (n random : ℕ) (bits : BitString) :
    ∃ ticks≤17*n+8,(boot selector).Runs n bits (initialMemory selector random) ticks
      (.done (readyMemory selector n random)) := by
  let loaded := Command.loadedIndex (O := Event) (13 : Fin 35) (unitSymbol selector) n (initialMemory selector random)
  have load := Command.loadIndex_runs (O := Event) (13 : Fin 35) (unitSymbol selector) n bits
    (initialMemory selector random) (by simp [initialMemory])
  have store : loaded.store=FixedBlockRetry.loadedStore (unitSymbol selector) n := by
    simp [loaded,Command.loadedIndex,initialMemory,Memory.set,FixedBlockRetry.loadedStore]
  have bounded : loaded.indexHead≤n := le_rfl
  obtain ⟨setupTicks,setupCost,setupRun⟩ := (setup selector).runs bits loaded bounded
  have cost : setupTicks≤14*n+5 := by
    change setupTicks≤(FixedBlockRetry.setup (O := Event) (unitSymbol selector)).cost loaded.store at setupCost
    rw [store] at setupCost
    exact setupCost.trans (FixedBlockRetry.setup_cost (O := Event) (unitSymbol selector) n)
  have ready : {loaded with store:=(setup selector).eval loaded.store}=readyMemory selector n random := by
    change {loaded with store:=(FixedBlockRetry.setup (O := Event) (unitSymbol selector)).eval loaded.store}=_
    rw [store,FixedBlockRetry.setup_eval]
    rfl
  rw [ready] at setupRun
  refine ⟨3*n+1+setupTicks,by omega,?_⟩
  exact Command.Runs.seq _ _ _ _ _ _ _ load setupRun

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
