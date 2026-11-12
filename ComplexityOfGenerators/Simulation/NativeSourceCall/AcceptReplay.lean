import ComplexityOfGenerators.Simulation.NativeSourceCall.Replay
import ComplexityOfGenerators.Simulation.NativeSourceCall.AcceptEntry

/-! A full accepted source execution reaches cleanup with its exact output
and random cursor. The replay budget is linear in source elapsed time. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem replay_accept (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (length offset : ℕ) (output : List O)
    (source finishSource : Configuration M) (target : Configuration (machine (F := F) M))
    (ready : Ready M data fixed length offset output source target) (sourceTicks : ℕ)
    (path : M.Steps (generatorData length) (bits.drop offset) source sourceTicks finishSource)
    (word : List O) (accepted : M.observe (generatorData length) (bits.drop offset) finishSource=.halted (.accepted word)) :
    ∃ ticks finishTarget, ticks≤(4*length+12)*sourceTicks+2*length+3 ∧
      State M data fixed finishSource.work finishSource.visited
        (packet length finishSource.indexHead finishSource.workHead) .clearEnd finishSource.workHead finishTarget ∧
      (machine M).Steps data bits target ticks finishTarget ∧
      finishTarget.randomHead=offset+finishSource.randomHead ∧ finishTarget.output=output++word := by
  obtain ⟨replayTicks,replayed,time,finishReady,replayPath⟩ := replay_steps M data bits fixed length offset output source finishSource target ready sourceTicks path
  have sourceTable : M.transition finishSource.state none none
      (if finishSource.indexHead<length then some () else none) (finishSource.work finishSource.workHead)=.accept := by
    cases action : M.transition finishSource.state none none
        (if finishSource.indexHead<length then some () else none) (finishSource.work finishSource.workHead) with
    | accept => rfl
    | reject => simp [Machine.observe,generatorData,action] at accepted
    | step state write work input auxiliary index emit => simp [Machine.observe,generatorData,action] at accepted
    | readRandom no yes =>
        simp only [Machine.observe,generatorData,List.getElem?_nil,action] at accepted
        split_ifs at accepted <;> cases accepted
  have outputEqual : finishSource.output=word := by simpa [Machine.observe,generatorData,sourceTable] using accepted
  obtain ⟨done,doneState,entry,frame⟩ := accept_entry M data bits fixed finishSource.work finishSource.visited
    length finishSource.indexHead finishReady.index finishSource.workHead finishSource.state sourceTable replayed finishReady.represented
  refine ⟨replayTicks+(2*finishSource.indexHead+3),done,by have := finishReady.index; omega,doneState,
    replayPath.trans (machine M) entry,frame.random.trans finishReady.random,?_⟩
  rw [frame.output,finishReady.output,outputEqual]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
