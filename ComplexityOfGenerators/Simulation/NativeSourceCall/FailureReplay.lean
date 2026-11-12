import ComplexityOfGenerators.Simulation.NativeSourceCall.Replay
import ComplexityOfGenerators.Simulation.NativeSourceCall.Terminal

/-! Finite source failures remain genuine finite native outcomes. No accepted
output can be introduced by a source rejection or a missing random bit. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem replay_rejected (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (length offset : ℕ) (output : List O)
    (source finishSource : Configuration M) (target : Configuration (machine (F := F) M))
    (ready : Ready M data fixed length offset output source target) (sourceTicks : ℕ)
    (path : M.Steps (generatorData length) (bits.drop offset) source sourceTicks finishSource)
    (terminal : M.observe (generatorData length) (bits.drop offset) finishSource=.halted .rejected) :
    ∃ ticks, ticks≤(4*length+12)*sourceTicks+length+1 ∧
      (machine M).runFrom data bits target ticks=.halted .rejected := by
  obtain ⟨replayTicks,replayed,time,finishReady,replayPath⟩ := replay_steps M data bits fixed length offset output source finishSource target ready sourceTicks path
  have sourceTable : M.transition finishSource.state none none
      (if finishSource.indexHead<length then some () else none) (finishSource.work finishSource.workHead)=.reject := by
    cases action : M.transition finishSource.state none none
        (if finishSource.indexHead<length then some () else none) (finishSource.work finishSource.workHead) with
    | reject => rfl
    | accept => simp [Machine.observe,generatorData,action] at terminal
    | step state write work input auxiliary index emit => simp [Machine.observe,generatorData,action] at terminal
    | readRandom no yes =>
        simp only [Machine.observe,generatorData,List.getElem?_nil,action] at terminal
        split_ifs at terminal <;> cases terminal
  have endRun := rejected M data bits fixed finishSource.work finishSource.visited length finishSource.indexHead
    finishReady.index finishSource.workHead finishSource.state sourceTable replayed finishReady.represented
  refine ⟨replayTicks+(finishSource.indexHead+1),by have := finishReady.index; omega,?_⟩
  rw [(machine M).runFrom_add data bits target replayed replayTicks (replayPath.runFrom (machine M)),endRun]

theorem replay_exhausted (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (length offset : ℕ) (output : List O)
    (source finishSource : Configuration M) (target : Configuration (machine (F := F) M))
    (ready : Ready M data fixed length offset output source target) (sourceTicks : ℕ)
    (path : M.Steps (generatorData length) (bits.drop offset) source sourceTicks finishSource)
    (terminal : M.observe (generatorData length) (bits.drop offset) finishSource=.halted .exhausted) :
    ∃ ticks, ticks≤(4*length+12)*sourceTicks+length+1 ∧
      (machine M).runFrom data bits target ticks=.halted .exhausted := by
  obtain ⟨replayTicks,replayed,time,finishReady,replayPath⟩ := replay_steps M data bits fixed length offset output source finishSource target ready sourceTicks path
  obtain ⟨no,yes,sourceTable,absent⟩ : ∃ no yes,
      M.transition finishSource.state none none (if finishSource.indexHead<length then some () else none)
        (finishSource.work finishSource.workHead)=.readRandom no yes ∧
      (bits.drop offset)[finishSource.randomHead]?=none := by
    cases action : M.transition finishSource.state none none
        (if finishSource.indexHead<length then some () else none) (finishSource.work finishSource.workHead) with
    | reject => simp [Machine.observe,generatorData,action] at terminal
    | accept => simp [Machine.observe,generatorData,action] at terminal
    | step state write work input auxiliary index emit => simp [Machine.observe,generatorData,action] at terminal
    | readRandom no yes =>
        refine ⟨no,yes,rfl,?_⟩
        simp only [Machine.observe,generatorData,List.getElem?_nil,action] at terminal
        have beyond : ¬finishSource.randomHead<(bits.drop offset).length := by
          intro available
          simp [available] at terminal
          simp only [List.length_drop] at available
          omega
        exact List.getElem?_eq_none_iff.mpr (Nat.le_of_not_gt beyond)
  have targetAbsent : bits[replayed.randomHead]?=none := by
    rw [finishReady.random]
    simpa only [List.getElem?_drop] using absent
  have endRun := exhausted M data bits fixed finishSource.work finishSource.visited length finishSource.indexHead
    finishReady.index finishSource.workHead finishSource.state no yes sourceTable replayed finishReady.represented targetAbsent
  refine ⟨replayTicks+(finishSource.indexHead+1),by have := finishReady.index; omega,?_⟩
  rw [(machine M).runFrom_add data bits target replayed replayTicks (replayPath.runFrom (machine M)),endRun]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
