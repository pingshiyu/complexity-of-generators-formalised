import ComplexityOfGenerators.Simulation.OriginalHeaderController.Phase

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound)

theorem retry_total (n : ℕ) (bits : BitString) (m : Memory (Cell selector) Event 35)
    (state : FixedBlockRetry.State n (cap width clock n) m) (waiting : m.store 32=[]) :
    ∃ ticks≤FixedBlockRetry.loopBudget width (cap width clock) (phaseTime selector width clock) n
        ((bits.length-m.randomHead)/width n),∃ result,
      (retry selector width clock).Runs n bits m ticks result ∧
      FixedBlockRetry.selected (headerBit selector) result=
        FixedBlockRetry.scan (width n) (reference selector clock n)
          ((bits.length-m.randomHead)/width n) (bits.drop m.randomHead) ∧
      FixedBlockRetry.Finished n (cap width clock n) result ∧
      (match result with | .exhausted => True | .done finish => BoundedMachinePhase.Canonical selector finish.store) ∧
      (match result with | .exhausted => True | .done finish => finish.indexHead=m.indexHead) := by
  obtain ⟨ticks,cost,result,run,answer,finished,canonical,head⟩ :=
    FixedBlockRetry.loop_runs_at_index_with_post (unitSymbol selector) Symbol.bit width (cap width clock)
    (phaseTime selector width clock) (phase selector width clock) (headerBit selector) (reference selector clock)
    (phase_correct selector width clock) (phase_bound selector width clock) (phase_frame selector width clock)
    (BoundedMachinePhase.Canonical selector) (phase_canonical selector width clock) (restore_canonical selector)
    n ((bits.length-m.randomHead)/width n) n bits m state waiting le_rfl
      (BoundedMachinePhase.indexBudget width clock n) (BoundedMachinePhase.widthBudget width clock n) rfl
  cases result with
  | exhausted => exact ⟨ticks,cost,.exhausted,run,answer,finished,trivial,trivial⟩
  | done finish => exact ⟨ticks,cost,.done finish,run,answer,finished,canonical,head⟩

/-- A successful certificate prefix stops exactly after its first successful
full block. Its random consumption is independent of any later source calls. -/
theorem retry_prefix_success (n failures : ℕ) (bits : BitString) (m : Memory (Cell selector) Event 35)
    (state : FixedBlockRetry.State n (cap width clock n) m) (waiting : m.store 32=[])
    (enough : (failures+1)*width n≤bits.length-m.randomHead)
    (failed : ∀ k<failures,reference selector clock n ((bits.drop (m.randomHead+k*width n)).take (width n))=none)
    (header : List Bool)
    (accepted : reference selector clock n ((bits.drop (m.randomHead+failures*width n)).take (width n))=some header) :
    ∃ ticks≤(failures+1)*(FixedBlockRetry.attemptBudget width (cap width clock) (phaseTime selector width clock) n+2),
      ∃ finish,(retry selector width clock).Runs n bits m ticks (.done finish) ∧
      FixedBlockRetry.State n (cap width clock n) finish ∧ finish.indexHead=m.indexHead ∧
      finish.randomHead=m.randomHead+(failures+1)*width n ∧ finish.store 31=header.map Symbol.letter := by
  induction failures generalizing m with
  | zero =>
      have blockFits : width n≤bits.length-m.randomHead := by simpa using enough
      obtain ⟨ticks,cost,next,run,nextState,nextIndex,nextRandom,canonical,flag,payload⟩ :=
        FixedBlockRetry.attempt_full_at_index_with_post (unitSymbol selector) Symbol.bit width (cap width clock)
          (phaseTime selector width clock) (phase selector width clock) (headerBit selector) (reference selector clock)
          (phase_correct selector width clock) (phase_bound selector width clock) (phase_frame selector width clock)
          (BoundedMachinePhase.Canonical selector) (phase_canonical selector width clock) (restore_canonical selector)
          n n bits m state le_rfl (BoundedMachinePhase.indexBudget width clock n)
            (BoundedMachinePhase.widthBudget width clock n) blockFits
      have first : reference selector clock n ((bits.drop m.randomHead).take (width n))=some header := by
        simpa only [Nat.zero_mul,Nat.add_zero] using accepted
      have found : next.store 32=[unitSymbol selector] := by simpa only [first,FixedBlockRetry.flagWord,Option.isSome_some,ite_true] using flag
      have stop : (retry selector width clock).Runs n bits next 0 (.done next) :=
        Command.Runs.loop_stop next 32 _ _ (by simp [observe,found])
      have loop := Command.Runs.loop m next 32 (fun observed => observed.1.isNone)
        (FixedBlockRetry.attempt (unitSymbol selector) Symbol.bit width (phase selector width clock))
        ticks 0 (.done next) (by simp [observe,waiting]) run stop
      refine ⟨1+ticks+1+0,by simp only [Nat.zero_add,Nat.one_mul]; omega,next,loop,nextState,nextIndex,?_,?_⟩
      · simpa only [Nat.zero_add,Nat.one_mul] using nextRandom
      · exact canonical.eq_of_filterMap selector header (payload header first)
  | succ failures ih =>
      have blockFits : width n≤bits.length-m.randomHead := by nlinarith
      obtain ⟨ticks,cost,next,run,nextState,nextIndex,nextRandom,canonical,flag,payload⟩ :=
        FixedBlockRetry.attempt_full_at_index_with_post (unitSymbol selector) Symbol.bit width (cap width clock)
          (phaseTime selector width clock) (phase selector width clock) (headerBit selector) (reference selector clock)
          (phase_correct selector width clock) (phase_bound selector width clock) (phase_frame selector width clock)
          (BoundedMachinePhase.Canonical selector) (phase_canonical selector width clock) (restore_canonical selector)
          n n bits m state le_rfl (BoundedMachinePhase.indexBudget width clock n)
            (BoundedMachinePhase.widthBudget width clock n) blockFits
      have first : reference selector clock n ((bits.drop m.randomHead).take (width n))=none := by
        simpa only [Nat.zero_mul,Nat.add_zero] using failed 0 (Nat.zero_lt_succ failures)
      have nextWaiting : next.store 32=[] := by simpa only [first,FixedBlockRetry.flagWord,Option.isSome_none,Bool.false_eq_true,ite_false] using flag
      have tailFits : (failures+1)*width n≤bits.length-next.randomHead := by
        rw [nextRandom,Nat.sub_add_eq]
        have total : (failures+1)*width n+width n≤bits.length-m.randomHead := by nlinarith
        omega
      have shifted (k : ℕ) : next.randomHead+k*width n=m.randomHead+(k+1)*width n := by
        rw [nextRandom]
        ring
      have tailFailed : ∀ k<failures,reference selector clock n ((bits.drop (next.randomHead+k*width n)).take (width n))=none := by
        intro k before
        rw [shifted]
        exact failed (k+1) (by omega)
      have tailAccepted : reference selector clock n ((bits.drop (next.randomHead+failures*width n)).take (width n))=some header := by
        rw [shifted]
        exact accepted
      obtain ⟨restTicks,restCost,finish,restRun,finishState,finishIndex,finishRandom,finishHeader⟩ :=
        ih next nextState nextWaiting tailFits tailFailed tailAccepted
      have loop := Command.Runs.loop m next 32 (fun observed => observed.1.isNone)
        (FixedBlockRetry.attempt (unitSymbol selector) Symbol.bit width (phase selector width clock))
        ticks restTicks (.done finish) (by simp [observe,waiting]) run restRun
      refine ⟨1+ticks+1+restTicks,by nlinarith,finish,loop,finishState,finishIndex.trans nextIndex,?_,finishHeader⟩
      rw [finishRandom,nextRandom]
      ring

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
