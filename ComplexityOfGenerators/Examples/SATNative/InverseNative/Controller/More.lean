import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Bit

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] InverseNative.bodyTransform transform

def morePrepared (m : Memory) : Memory := {m with store := moreRoutine.eval m.store}

def moreBitBudget (bit : Bool) (n : ℕ) (bits : BitString) (m : Memory) : ℕ :=
  moreRoutine.cost m.store+(if (m.store 10).length+1 ≤ (m.store 4).length then
    finishBitBudget bit n bits (morePrepared m) else 0)+bits.length+4

def bitOutcome (bit : Bool) (capacity active : ℕ) (formula : Formula) (n : ℕ) (bits : BitString) : Outcome Symbol :=
  if active+1 ≤ capacity ∧ n ≤ bits.length then
    .accepted ((formula.lift active bit (choiceRows formula (bits.take n))).encode capacity (active+1))
  else .exhausted

theorem moreBit_runs (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (n : ℕ) (bits : BitString) (m : Memory)
    (index : m.indexHead ≤ n) (counter : m.store 32 = List.replicate n .zero)
    (represented : Represents capacity active ⟨formula.bodyWord capacity,false,false,true⟩ m.store)
    (clock : NativeBody.tokenCount formula ≤ (m.store 16).length)
    (random : m.randomHead = 0) (output : m.output = []) :
    ∃ ticks ≤ moreBitBudget bit n bits m, ∃ result,
      (moreBit bit).Runs n bits m ticks result ∧ result.outcome = bitOutcome bit capacity active formula n bits := by
  obtain ⟨firstTicks,firstCost,firstRun⟩ := moreRoutine.runs bits m index
  let ready := morePrepared m
  have readyRep := moreRoutine_represents capacity active _ m.store represented
  have readyClock : NativeBody.tokenCount formula ≤ (ready.store 16).length := by
    rw [show ready.store 16 = m.store 16 from moreRoutine_frame m.store 16 (by decide) (by decide) (by decide) (by decide)]
    exact clock
  have readyCounter : ready.store 32 = List.replicate n .zero :=
    (moreRoutine_frame m.store 32 (by decide) (by decide) (by decide) (by decide)).trans counter
  have cap : m.store 4 = List.replicate capacity .one := represented.2.1
  have count : m.store 10 = List.replicate active .one := represented.2.2.1
  have flag : (ready.store 27).head?.isSome = decide (active+1 ≤ capacity) := moreRoutine_flag m.store capacity active cap count
  by_cases more : active+1 ≤ capacity
  · by_cases enough : n ≤ bits.length
    · obtain ⟨lastTicks,lastCost,final,lastRun,lastOutput⟩ := finishBit_full bit bound formula valid n bits ready index readyCounter readyRep readyClock
        (by simpa only [ready,morePrepared,random,Nat.zero_add] using enough)
      have branch : (Command.branch 27 fun remaining => if remaining.1.isSome then finishBit bit else .drain).Runs
          n bits ready (1+lastTicks) (.done final) := by
        apply Command.Runs.branch
        simpa only [observe,flag,decide_eq_true more,ite_true] using lastRun
      have run := Command.Runs.seq _ _ _ _ _ _ _ firstRun branch
      refine ⟨firstTicks+1+(1+lastTicks),?_,.done final,run,?_⟩
      · change lastTicks ≤ finishBitBudget bit n bits (morePrepared m) at lastCost
        dsimp only [moreBitBudget]
        rw [if_pos (by simpa [cap,count] using more)]
        omega
      · simpa [Result.outcome,bitOutcome,more,enough,ready,morePrepared,random,output] using lastOutput
    · obtain ⟨lastTicks,lastCost,lastRun⟩ := finishBit_short bit n bits ready index readyCounter
        (by change m.randomHead ≤ bits.length; rw [random]; omega)
        (by change bits.length < m.randomHead+n; rw [random,Nat.zero_add]; omega)
      have branch : (Command.branch 27 fun remaining => if remaining.1.isSome then finishBit bit else .drain).Runs
          n bits ready (1+lastTicks) .exhausted := by
        apply Command.Runs.branch
        simpa only [observe,flag,decide_eq_true more,ite_true] using lastRun
      have run := Command.Runs.seq _ _ _ _ _ _ _ firstRun branch
      refine ⟨firstTicks+1+(1+lastTicks),?_,.exhausted,run,?_⟩
      · change lastTicks ≤ finishBitBudget bit n bits (morePrepared m) at lastCost
        dsimp only [moreBitBudget]
        rw [if_pos (by simpa [cap,count] using more)]
        omega
      · simp [Result.outcome,bitOutcome,enough]
  · have branch : (Command.branch 27 fun remaining => if remaining.1.isSome then finishBit bit else .drain).Runs
        n bits ready (1+bits.length) .exhausted := by
      apply Command.Runs.branch
      have zero : ready.randomHead = 0 := random
      have drainRun : Command.drain.Runs n bits ready bits.length .exhausted := by
        simpa only [zero,Nat.sub_zero] using Command.Runs.drain (n := n) (bits := bits) ready
      simpa only [observe,flag,decide_eq_false more,Bool.false_eq_true,ite_false] using drainRun
    have run := Command.Runs.seq _ _ _ _ _ _ _ firstRun branch
    refine ⟨firstTicks+1+(1+bits.length),?_,.exhausted,run,?_⟩
    · dsimp only [moreBitBudget]
      rw [if_neg (by simpa [cap,count] using more)]
      omega
    · simp [Result.outcome,bitOutcome,more]

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
