import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Execution
import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Total

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

theorem emit_runs (inputIndex : ℕ) (bits : BitString) (m : Memory (Cell (β := β) P) α 80)
    (head : m.indexHead ≤ inputIndex) :
    ∃ ticks ≤ 3*(m.store 74).length+10*(m.store 70).length+2, ∃ next,
      (emit P).Runs inputIndex bits m ticks (.done next) ∧
      next.output = m.output ++ ((m.store 70).filterMap (outputLetter P)).reverse ∧
      next.indexHead = m.indexHead ∧ next.randomHead = m.randomHead := by
  let a : Memory (Cell (β := β) P) α 80 := {m with store := (Routine.clear (O := α) 74).eval m.store}
  let b : Memory (Cell (β := β) P) α 80 := {a with store := (Routine.transfer (O := α) 70 74 (by decide) id).eval a.store}
  obtain ⟨first, firstCost, firstRun⟩ := (Routine.clear (O := α) 74).runs (n := inputIndex) bits m head
  obtain ⟨second, secondCost, secondRun⟩ := (Routine.transfer (O := α) 70 74 (by decide) id).runs (n := inputIndex) bits a head
  have lastRun := Command.emitWord_runs (74 : Fin 80) (outputLetter P) bits b head
  have stored : b.store 74 = (m.store 70).reverse := by simp [b, a, Routine.transfer, Routine.clear]
  refine ⟨first+1+(second+1+4*(b.store 74).length), ?_, Command.emitted 74 (outputLetter P) b, ?_, ?_, rfl, rfl⟩
  · change first ≤ 3*(m.store 74).length at firstCost
    change second ≤ 6*(a.store 70).length at secondCost
    have source : a.store 70 = m.store 70 := by simp [a, Routine.clear]
    rw [source] at secondCost
    rw [stored, List.length_reverse]
    omega
  · exact Command.Runs.seq _ _ _ _ _ _ _ firstRun (Command.Runs.seq _ _ _ _ _ _ _ secondRun lastRun)
  · change m.output ++ (b.store 74).filterMap (outputLetter P) = _
    rw [stored, List.filterMap_reverse]

variable (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

include retract in
theorem command_runs_trace (inputIndex ceiling budget : ℕ) (parts : List ℕ) (records : List (Record α))
    (bits : BitString) (m : Memory (Cell (β := β) P) α 80)
    (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode parts) (sizes : StoreBound m.store budget)
    (indices : ∀ j ∈ parts, j ≤ inputIndex)
    (fits : budget+parts.length*BoundedMachinePhase.cap P.seed P.clock inputIndex ≤ ceiling)
    (trace : Trace P bits m.randomHead parts records) :
    ∃ ticks ≤ (blocks records+1)*coefficient P inputIndex ceiling,
      ∃ next, (command P decode).Runs inputIndex bits m ticks (.done next) ∧
        next.indexHead = 0 ∧ next.randomHead = m.randomHead+consumed P parts records ∧ next.output = [] ∧
        (next.store 70).filterMap (outputLetter P) = (words records).reverse ∧
        StoreBound next.store (budget+parts.length*BoundedMachinePhase.cap P.seed P.clock inputIndex) := by
  let ready : Memory (Cell (β := β) P) α 80 := {m with store := (Routine.clear (O := α) 70).eval m.store}
  have readyBound : StoreBound ready.store budget := sizes.clear 70
  have readyPath : ready.store 31 = pathWord P encode parts := by simpa [ready, Routine.clear] using path
  obtain ⟨first, firstCost, firstRun⟩ := (Routine.clear (O := α) 70).runs (n := inputIndex) bits m (by omega)
  obtain ⟨rest, restCost, next, restRun, post, finalBound⟩ := loop_runs_trace P encode decode retract inputIndex ceiling budget
    parts records bits ready origin empty readyPath readyBound indices fits trace
  refine ⟨first+1+rest, ?_, next, Command.Runs.seq _ _ _ _ _ _ _ firstRun restRun,
    post.origin.trans origin, post.random, post.output, ?_, finalBound⟩
  · change first ≤ 3*(m.store 70).length at firstCost
    have small : budget ≤ ceiling := by omega
    have charge : first+1 ≤ coefficient P inputIndex ceiling := by
      have size := sizes 70
      unfold coefficient
      omega
    nlinarith only [restCost, charge]
  · simpa [ready, Routine.clear] using post.buffer

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
