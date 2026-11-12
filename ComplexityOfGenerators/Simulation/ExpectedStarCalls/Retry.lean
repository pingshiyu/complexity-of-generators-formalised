import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Views

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

def startMemory (j : ℕ) (m : Memory (Cell (β := β) P) α 80) : Memory (InnerCell P) α 35 :=
  ⟨(), m.indexHead, m.randomHead, m.output, initialStore P j⟩

theorem startMemory_state (j : ℕ) (m : Memory (Cell (β := β) P) α 80)
    (origin : m.indexHead = 0) (empty : m.output = []) :
    FixedBlockRetry.State j (BoundedMachinePhase.cap P.seed P.clock j) (startMemory P j m) := by
  refine ⟨by simp [startMemory, origin], ?_, ?_, empty, ?_⟩
  · simp [startMemory, initialStore]
  · simp [startMemory, initialStore]
  · exact (initialStore_bound P j).mono (by have := BoundedMachinePhase.indexBudget P.seed P.clock j; omega)

theorem retry_lift {inputIndex j ticks : ℕ} {bits : BitString} {m : Memory (Cell (β := β) P) α 80}
    {result : Result (InnerCell P) α 35}
    (owned : ∀ i, m.store (innerSlots i) = (initialStore P j i).map Sum.inr)
    (run : (FixedBlockRetry.retryLoop UnionGenerator.Symbol.unit UnionGenerator.Symbol.bit P.seed
      (BoundedMachinePhase.phase P.machine P.seed P.clock)).Runs inputIndex bits (startMemory P j m) ticks result) :
    (retry P).Runs inputIndex bits m ticks ((result.mapSymbols Sum.inr).patch innerSlots m) := by
  have mapped := run.mapSymbols (Sum.inr : InnerCell P → Cell (β := β) P) (innerDecode P) (by intro symbol; rfl)
  have lifted := mapped.rename innerSlots m
  have initialEq : Memory.patch innerSlots ((startMemory P j m).mapSymbols Sum.inr) m = m := by
    apply Memory.patch_eq
    apply Configuration.ext <;> try rfl
    funext i
    exact owned i
  rwa [initialEq] at lifted

def callBudget (j : ℕ) : ℕ :=
  FixedBlockRetry.attemptBudget P.seed (BoundedMachinePhase.cap P.seed P.clock)
    (BoundedMachinePhase.time P.machine P.seed P.clock) j+2

/-- Lift the actual source-phase retry loop into the disjoint inner bank.
No word is emitted, and the outer read-only index head is preserved exactly. -/
theorem retry_runs_success (inputIndex j failures : ℕ) (word : List α) (bits : BitString)
    (m : Memory (Cell (β := β) P) α 80) (origin : m.indexHead = 0) (empty : m.output = [])
    (owned : ∀ i, m.store (innerSlots i) = (initialStore P j i).map Sum.inr)
    (within : j ≤ inputIndex)
    (enough : m.randomHead+(failures+1)*P.seed j ≤ bits.length)
    (failed : ∀ k < failures, UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (m.randomHead+k*P.seed j)).take (P.seed j)) = none)
    (success : UnionGenerator.sourceValue P.machine P.clock j
      ((bits.drop (m.randomHead+failures*P.seed j)).take (P.seed j)) = some word) :
    ∃ ticks ≤ (failures+1)*callBudget P j, ∃ next : Memory (InnerCell P) α 35,
      (retry P).Runs inputIndex bits m ticks
        (.done (Memory.patch innerSlots (next.mapSymbols Sum.inr) m)) ∧
      FixedBlockRetry.State j (BoundedMachinePhase.cap P.seed P.clock j) next ∧
      next.indexHead = 0 ∧ next.randomHead = m.randomHead+(failures+1)*P.seed j ∧
      (next.store 31).filterMap (UnionGenerator.outputLetter P.machine P.machine) = word := by
  let start := startMemory P j m
  have startState := startMemory_state P j m origin empty
  obtain ⟨ticks, cost, next, run, state, nextOrigin, nextHead, _, payload⟩ :=
    FixedBlockRetry.loop_runs_success_at_index_preserves_head
      (UnionGenerator.Symbol.unit : InnerCell P) UnionGenerator.Symbol.bit P.seed
      (BoundedMachinePhase.cap P.seed P.clock) (BoundedMachinePhase.time P.machine P.seed P.clock)
      (BoundedMachinePhase.phase P.machine P.seed P.clock) (UnionGenerator.outputLetter P.machine P.machine)
      (fun n block => UnionGenerator.sourceValue P.machine P.clock n block)
      (BoundedMachinePhase.phase_correct P.machine P.seed P.clock)
      (BoundedMachinePhase.phase_bound P.machine P.seed P.clock)
      (fun s => congrArg List.length (BoundedMachinePhase.phase_fixes22 P.machine P.seed P.clock s))
      j failures inputIndex bits start startState (by simp [start, startMemory, initialStore]) within
      (BoundedMachinePhase.indexBudget P.seed P.clock j) (BoundedMachinePhase.widthBudget P.seed P.clock j)
      enough failed word success
  have lifted := retry_lift P owned run
  refine ⟨ticks, cost, next, lifted, state, ?_, nextHead, payload⟩
  exact nextOrigin.trans origin

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
