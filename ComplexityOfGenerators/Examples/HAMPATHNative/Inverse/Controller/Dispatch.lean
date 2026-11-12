import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Random

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

noncomputable def dispatchBudget (bits : BitString) (m : Memory) : ℕ :=
  4*(m.store 32).length+randomBudget bits m+bits.length+3

theorem dispatch_runs {n : ℕ} (bits : BitString) (m : Memory) (index : m.indexHead≤n)
    (graph : Graph) (start : ℕ) (word : List Symbol) (inside : start<graph.size)
    (result : Classify.Result m.store graph start n word) (random : m.randomHead=0) (output : m.output=[]) :
    ∃ ticks≤dispatchBudget bits m, ∃ final,
      dispatch.Runs n bits m ticks final ∧ final.outcome=valueOutcome (value graph start n word bits) := by
  cases live : (m.store 41).head?.isSome with
  | false =>
      have run : dispatch.Runs n bits m (1+bits.length) .exhausted := by
        apply Command.Runs.branch
        simpa only [observe,live,Bool.false_eq_true,ite_false,random,Nat.sub_zero] using
          (Command.Runs.drain (n := n) (bits := bits) m)
      refine ⟨1+bits.length,by unfold dispatchBudget; omega,.exhausted,run,?_⟩
      have dead : Classify.enabled n graph.size word=false := result.live.symm.trans live
      rw [value_disabled graph start n word bits dead]
      rfl
  | true =>
      by_cases empty : word=[]
      · have facts : BaseSearch.Productive n ∧ graph.size=1 := by
          simpa [Classify.enabled,empty,Bool.and_eq_true] using result.live.symm.trans live
        obtain ⟨final,emitRun,emitted⟩ := emit_runs 32 bits m index
        have labelEmpty : (m.store 33).head?.isNone=true := by simp [result.labelWord,empty]
        have labelRun : (Command.branch 33 fun label => if label.1.isNone then emit 32 else randomPhase).Runs n bits m
            (1+4*(m.store 32).length) (.done final) := by
          apply Command.Runs.branch
          simpa only [observe,labelEmpty,ite_true] using emitRun
        have run : dispatch.Runs n bits m (1+(1+4*(m.store 32).length)) (.done final) := by
          apply Command.Runs.branch
          simpa only [observe,live,ite_true] using labelRun
        refine ⟨1+(1+4*(m.store 32).length),by unfold dispatchBudget; omega,.done final,run,?_⟩
        change Outcome.accepted final.output=valueOutcome (value graph start n word bits)
        rw [emitted,result.raw,output]
        simp [value,empty,facts.1,facts.2,valueOutcome]
      · obtain ⟨ticks,cost,final,run,outcome⟩ := randomPhase_runs bits m index graph start word inside result empty live random output
        have labelPresent : (m.store 33).head?.isNone=false := by cases word <;> simp_all [result.labelWord]
        have labelRun : (Command.branch 33 fun label => if label.1.isNone then emit 32 else randomPhase).Runs n bits m
            (1+ticks) final := by
          apply Command.Runs.branch
          simpa only [observe,labelPresent,Bool.false_eq_true,ite_false] using run
        have fullRun : dispatch.Runs n bits m (1+(1+ticks)) final := by
          apply Command.Runs.branch
          simpa only [observe,live,ite_true] using labelRun
        exact ⟨1+(1+ticks),by unfold dispatchBudget; omega,final,fullRun,outcome⟩

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
