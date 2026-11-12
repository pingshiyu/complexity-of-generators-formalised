import ComplexityOfGenerators.Simulation.OriginalHeaderController.Boot
import ComplexityOfGenerators.Simulation.OriginalHeaderController.Retry
import ComplexityOfGenerators.Simulation.WordStack.NoEmission

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound)

theorem erase_empty (m : Memory (Cell selector) Event 35) (empty : m.output=[]) :
    m.filterMapOutput (fun _ : Event => (none : Option Event))=m := by
  apply Configuration.ext <;> try rfl
  simp [Memory.filterMapOutput,empty]

theorem prelude_noEmit : ((prelude selector width clock).program 0).NoEmit :=
  (Command.outputFree_erased ((boot selector).seq (retry selector width clock))).noEmit 0

theorem prelude_success (n random failures : ℕ) (bits : BitString)
    (enough : random+(failures+1)*width n≤bits.length)
    (failed : ∀ k<failures,reference selector clock n ((bits.drop (random+k*width n)).take (width n))=none)
    (header : List Bool)
    (accepted : reference selector clock n ((bits.drop (random+failures*width n)).take (width n))=some header) :
    ∃ ticks≤17*n+9+(failures+1)*(FixedBlockRetry.attemptBudget width (cap width clock) (phaseTime selector width clock) n+2),
      ∃ finish,(prelude selector width clock).Runs n bits (initialMemory selector random) ticks (.done finish) ∧
        FixedBlockRetry.State n (cap width clock n) finish ∧
        finish.randomHead=random+(failures+1)*width n ∧ finish.store 31=header.map Symbol.letter := by
  obtain ⟨bootTicks,bootBound,bootRun⟩ := boot_runs selector n random bits
  have waiting : (readyMemory selector n random).store 32=[] := by simp [readyMemory,readyStore]
  obtain ⟨retryTicks,retryBound,finish,retryRun,finishState,_,finishRandom,finishHeader⟩ :=
    retry_prefix_success selector width clock n failures bits (readyMemory selector n random)
      (ready_state selector width clock n random) waiting (by simpa only [readyMemory] using (show
        (failures+1)*width n≤bits.length-random by omega))
      (by simpa only [readyMemory] using failed) header (by simpa only [readyMemory] using accepted)
  have raw := Command.Runs.seq _ _ _ _ _ _ _ bootRun retryRun
  have mapped := raw.filterMapOutput (fun _ : Event => (none : Option Event))
  rw [erase_empty selector _ rfl,Result.filterMapOutput,erase_empty selector _ finishState.output] at mapped
  exact ⟨bootTicks+1+retryTicks,by omega,finish,mapped,finishState,finishRandom,finishHeader⟩

theorem prelude_total (n random : ℕ) (bits : BitString) :
    ∃ ticks result,(prelude selector width clock).Runs n bits (initialMemory selector random) ticks result ∧
      (match result with
      | .exhausted => True
      | .done finish => FixedBlockRetry.State n (cap width clock n) finish ∧
          BoundedMachinePhase.Canonical selector finish.store ∧
          FixedBlockRetry.selected (headerBit selector) result=
            FixedBlockRetry.scan (width n) (reference selector clock n)
              ((bits.length-random)/width n) (bits.drop random)) := by
  obtain ⟨bootTicks,_,bootRun⟩ := boot_runs selector n random bits
  have waiting : (readyMemory selector n random).store 32=[] := by simp [readyMemory,readyStore]
  obtain ⟨retryTicks,_,result,retryRun,answer,finished,canonical,_⟩ :=
    retry_total selector width clock n bits (readyMemory selector n random)
      (ready_state selector width clock n random) waiting
  have raw := Command.Runs.seq _ _ _ _ _ _ _ bootRun retryRun
  have mapped := raw.filterMapOutput (fun _ : Event => (none : Option Event))
  rw [erase_empty selector _ rfl] at mapped
  cases result with
  | exhausted => exact ⟨bootTicks+1+retryTicks,.exhausted,mapped,trivial⟩
  | done finish =>
      rw [Result.filterMapOutput,erase_empty selector _ finished.1.output] at mapped
      exact ⟨bootTicks+1+retryTicks,.done finish,mapped,finished.1,canonical,answer⟩

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
