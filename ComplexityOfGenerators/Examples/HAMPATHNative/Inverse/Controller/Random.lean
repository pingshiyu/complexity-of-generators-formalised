import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Sampling

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

theorem randomPhase_runs {n : ℕ} (bits : BitString) (m : Memory) (index : m.indexHead≤n)
    (graph : Graph) (start : ℕ) (word : List Symbol) (inside : start<graph.size)
    (result : Classify.Result m.store graph start n word) (nonempty : word≠[])
    (live : (m.store 41).head?.isSome=true) (random : m.randomHead=0) (output : m.output=[]) :
    ∃ ticks≤randomBudget bits m, ∃ final,
      randomPhase.Runs n bits m ticks final ∧
        final.outcome=valueOutcome (value graph start n word bits) := by
  obtain ⟨productive,capacity,next,decoded,nextWord⟩ := enabled_inputs m.store graph start n word result nonempty live
  let count := width (graph.size+1)+2*graph.size
  obtain ⟨clockTicks,clockCost,clockRun⟩ := Choose.sampleClock.runs (n := n) bits m index
  change Choose.sampleClock.command.Runs n bits m clockTicks (.done (counted m)) at clockRun
  have countLength : ((counted m).store 46).length=count := counted_count m graph start n word result
  have source42 : (counted m).store 42=m.store 42 := by simp [counted,Choose.sampleClock_eval]
  have source47 : (counted m).store 47=m.store 47 := by simp [counted,Choose.sampleClock_eval]
  by_cases enough : count≤bits.length
  · obtain ⟨collectTicks,collectCost,collectRun⟩ := Command.collectForward_full (46 : Fin 64) 42 47
      (by decide) (by decide) (by decide) Symbol.bit bits (counted m) index (by
        change m.randomHead+((counted m).store 46).length≤bits.length
        rw [random,countLength]
        simpa using enough)
    change (Command.collectForward 46 42 47 (by decide) Symbol.bit).Runs n bits (counted m) collectTicks
      (.done (sampled bits m)) at collectRun
    rw [source42,source47] at collectCost
    obtain ⟨chooseTicks,chooseCost,chooseRun⟩ := Choose.routine.runs (n := n) bits (sampled bits m) index
    change Choose.routine.command.Runs n bits (sampled bits m) chooseTicks (.done (chosen bits m)) at chooseRun
    let window := bits.take count
    have windowLength : window.length=count := by simp [window,Nat.min_eq_left enough]
    have windowEnough : width (graph.size+1)+2*graph.size≤window.length := by rw [windowLength]
    have sampledResult := sampled_result bits m graph start n word result
    have sourceWindow : (sampled bits m).store 42=window.map Symbol.bit := sampled_bits bits m graph start n word result random
    have sampledLive : ((sampled bits m).store 41).head?.isSome=true :=
      sampledResult.live.trans (result.live.symm.trans live)
    have fields := chosen_fields (sampled bits m).store graph start n next word sampledResult
      nonempty decoded window sourceWindow inside windowEnough
    cases selected : Position.value graph.size start next
        (FixedBitBlocks.decode (window.take (width (graph.size+1)))) with
    | none =>
        have dead : ((chosen bits m).store 41).head?.isSome=false := by
          change (Choose.routine.eval (sampled bits m).store 41).head?.isSome=false
          rw [fields.live,selected]
          rfl
        have finishRun := finish_dead (n := n) bits (chosen bits m) dead
        have tailRun := Command.Runs.seq _ _ _ _ _ _ _ chooseRun finishRun
        have middleRun := Command.Runs.seq _ _ _ _ _ _ _ collectRun tailRun
        have fullRun := Command.Runs.seq _ _ _ _ _ _ _ clockRun middleRun
        refine ⟨clockTicks+1+(collectTicks+1+(chooseTicks+1+(1+(bits.length-(chosen bits m).randomHead)))),?_,.exhausted,fullRun,?_⟩
        · change _≤randomBudget bits m
          unfold randomBudget
          have drainBound : bits.length-(chosen bits m).randomHead≤bits.length := Nat.sub_le _ _
          omega
        · have noValue := value_bad_position graph start n next word window productive nonempty capacity decoded windowEnough selected
          have same := value_take graph start n word bits enough
          change valueOutcome none=valueOutcome (value graph start n word bits)
          rw [← same,noValue]
    | some position =>
        have chosenValue := chosen_output (sampled bits m).store graph start n next position word sampledResult
          nonempty decoded window sourceWindow inside windowEnough selected
        have afterLive : ((chosen bits m).store 41).head?.isSome=true := by
          change (Choose.routine.eval (sampled bits m).store 41).head?.isSome=true
          rw [chosenValue.2]
          exact sampledLive
        obtain ⟨finishTicks,finishCost,final,finishRun,finishedOutput⟩ := finish_live bits (chosen bits m) index afterLive
        have tailRun := Command.Runs.seq _ _ _ _ _ _ _ chooseRun finishRun
        have middleRun := Command.Runs.seq _ _ _ _ _ _ _ collectRun tailRun
        have fullRun := Command.Runs.seq _ _ _ _ _ _ _ clockRun middleRun
        refine ⟨clockTicks+1+(collectTicks+1+(chooseTicks+1+finishTicks)),?_,.done final,fullRun,?_⟩
        · unfold randomBudget
          omega
        · have generated := value_decoded graph start n next position word window productive nonempty capacity decoded windowEnough selected
          have same := value_take graph start n word bits enough
          change Outcome.accepted final.output=valueOutcome (value graph start n word bits)
          rw [← same,generated]
          change Outcome.accepted final.output=Outcome.accepted _
          apply congrArg Outcome.accepted
          rw [finishedOutput]
          change (chosen bits m).output++(Output.routine (O := Symbol)).eval
            (Choose.routine.eval (sampled bits m).store) 31=_
          rw [chosenValue.1]
          simp [chosen,sampled,Command.forwardCollected,counted,output]
  · obtain ⟨collectTicks,collectCost,collectRun⟩ := Command.collectForward_short (46 : Fin 64) 42 47
      (by decide) (by decide) (by decide) Symbol.bit bits (counted m) index (by
        change bits.length-m.randomHead<((counted m).store 46).length
        rw [random,countLength]
        omega)
    rw [source42,source47] at collectCost
    have tailRun := Command.Runs.seq_absent (counted m) (Command.collectForward 46 42 47 (by decide) Symbol.bit)
      (Choose.routine.command.seq finish) collectTicks collectRun
    have fullRun := Command.Runs.seq _ _ _ _ _ _ _ clockRun tailRun
    refine ⟨clockTicks+1+collectTicks,?_,.exhausted,fullRun,?_⟩
    · unfold randomBudget
      omega
    · change valueOutcome none=valueOutcome (value graph start n word bits)
      rw [value_short graph start n word nonempty bits (by omega)]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
