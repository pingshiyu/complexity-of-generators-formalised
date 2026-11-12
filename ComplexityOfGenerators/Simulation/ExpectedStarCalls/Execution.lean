import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Bounds
import ComplexityOfGenerators.Simulation.ExpectedStarCalls.Trace

namespace ComplexityOfGenerators.Simulation.ExpectedStarCalls
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α β : Type} [Fintype α] [Fintype β] (P : BoundedPhaseFamily α)

def coefficient (n ceiling : ℕ) : ℕ :=
  callBudget P n+1000*(ceiling+BoundedMachinePhase.cap P.seed P.clock n+1)+10

structure LoopPost (before after : Memory (Cell (β := β) P) α 80)
    (parts : List ℕ) (records : List (Record α)) : Prop where
  origin : after.indexHead = before.indexHead
  random : after.randomHead = before.randomHead+consumed P parts records
  output : after.output = []
  path : after.store 31 = []
  buffer : (after.store 70).filterMap (outputLetter P) = (words records).reverse ++ (before.store 70).filterMap (outputLetter P)
  master : after.store 22 = before.store 22

variable (encode : StarPaths.Symbol → β) (decode : β → StarPaths.Symbol)
    (retract : Function.LeftInverse decode encode)

include retract in
theorem loop_runs_trace (inputIndex ceiling budget : ℕ) (parts : List ℕ) (records : List (Record α))
    (bits : BitString) (m : Memory (Cell (β := β) P) α 80)
    (origin : m.indexHead = 0) (empty : m.output = [])
    (path : m.store 31 = pathWord P encode parts) (sizes : StoreBound m.store budget)
    (indices : ∀ j ∈ parts, j ≤ inputIndex)
    (fits : budget+parts.length*BoundedMachinePhase.cap P.seed P.clock inputIndex ≤ ceiling)
    (trace : Trace P bits m.randomHead parts records) :
    ∃ ticks ≤ blocks records*coefficient P inputIndex ceiling,
      ∃ next, (loop P decode).Runs inputIndex bits m ticks (.done next) ∧
        LoopPost P m next parts records ∧
        StoreBound next.store (budget+parts.length*BoundedMachinePhase.cap P.seed P.clock inputIndex) := by
  induction parts generalizing records budget m with
  | nil =>
      cases records with
      | cons record records => exact False.elim trace
      | nil =>
          have wordEmpty : m.store 31 = [] := by simpa [pathWord, StarPaths.payload] using path
          refine ⟨0, by simp [blocks], m, ?_, ?_, ?_⟩
          · exact Command.Runs.loop_stop m 31 _ _ (by simp [observe, wordEmpty])
          · exact ⟨rfl, by simp [consumed], empty, wordEmpty, by simp [words], rfl⟩
          · simpa using sizes
  | cons j parts ih =>
      cases records with
      | nil => exact False.elim trace
      | cons record records =>
          obtain ⟨enough, failed, success, later⟩ := trace
          have within : j ≤ inputIndex := indices j (by simp)
          have capBound := polynomial_mono (BoundedMachinePhase.cap P.seed P.clock) within
          obtain ⟨first, firstCost, after, firstRun, firstPost, afterBound⟩ :=
            call_runs_success_bounded P encode decode retract inputIndex j record.failures budget parts record.word bits m
              origin empty sizes path within enough failed success
          change first ≤ record.blocks*callBudget P j+300*(budget+BoundedMachinePhase.cap P.seed P.clock j+1) at firstCost
          have afterOrigin : after.indexHead = 0 := firstPost.origin.trans origin
          have afterFits : budget+BoundedMachinePhase.cap P.seed P.clock j+
              parts.length*BoundedMachinePhase.cap P.seed P.clock inputIndex ≤ ceiling := by
            simp only [List.length_cons, Nat.add_mul, Nat.one_mul] at fits
            omega
          have afterTrace : Trace P bits after.randomHead parts records := by
            rw [firstPost.random]
            exact later
          obtain ⟨rest, restCost, next, restRun, restPost, endBound⟩ := ih
            (budget+BoundedMachinePhase.cap P.seed P.clock j) records after afterOrigin firstPost.output firstPost.path afterBound
            (fun k member => indices k (by simp [member])) afterFits afterTrace
          have callBound := callBudget_mono P within
          have budgetBound : budget ≤ ceiling := by omega
          have positive : 1 ≤ record.blocks := by simp [Record.blocks]
          have firstBudget : 1+first+1 ≤ record.blocks*coefficient P inputIndex ceiling := by
            have retries := Nat.mul_le_mul_left record.blocks callBound
            have overhead : 300*(budget+BoundedMachinePhase.cap P.seed P.clock j+1)+2 ≤
                1000*(ceiling+BoundedMachinePhase.cap P.seed P.clock inputIndex+1)+10 := by omega
            have scaled : 1000*(ceiling+BoundedMachinePhase.cap P.seed P.clock inputIndex+1)+10 ≤
                record.blocks*(1000*(ceiling+BoundedMachinePhase.cap P.seed P.clock inputIndex+1)+10) := by
              simpa only [Nat.one_mul] using Nat.mul_le_mul_right
                (1000*(ceiling+BoundedMachinePhase.cap P.seed P.clock inputIndex+1)+10) positive
            calc
              1+first+1 ≤ record.blocks*callBudget P j+(300*(budget+BoundedMachinePhase.cap P.seed P.clock j+1)+2) := by omega
              _ ≤ record.blocks*callBudget P inputIndex+(1000*(ceiling+BoundedMachinePhase.cap P.seed P.clock inputIndex+1)+10) := Nat.add_le_add retries overhead
              _ ≤ record.blocks*callBudget P inputIndex+record.blocks*(1000*(ceiling+BoundedMachinePhase.cap P.seed P.clock inputIndex+1)+10) := Nat.add_le_add_left scaled _
              _ = record.blocks*coefficient P inputIndex ceiling := by unfold coefficient; ring
          refine ⟨1+first+1+rest, ?_, next, ?_, ?_, ?_⟩
          · change 1+first+1+rest ≤ (record.blocks+blocks records)*coefficient P inputIndex ceiling
            nlinarith only [firstBudget, restCost]
          · exact Command.Runs.loop m after 31 (fun observation => observation.1.isSome) (call P decode)
              first rest (.done next) (by simp [observe, path, pathWord_cons]) firstRun restRun
          · constructor
            · exact restPost.origin.trans firstPost.origin
            · rw [restPost.random, firstPost.random]
              simp [consumed, Record.blocks, Nat.add_assoc]
            · exact restPost.output
            · exact restPost.path
            · rw [restPost.buffer, firstPost.buffer]
              simp [words, List.reverse_append, List.append_assoc]
            · exact restPost.master.trans (firstPost.frame 22 (outside_inner 22 (Or.inl (by decide)))
                (by decide) (by decide) (by decide) (by decide))
          · apply endBound.mono
            simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
            omega

end
end ComplexityOfGenerators.Simulation.ExpectedStarCalls
