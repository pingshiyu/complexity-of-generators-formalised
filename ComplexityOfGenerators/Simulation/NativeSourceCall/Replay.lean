import ComplexityOfGenerators.Simulation.NativeSourceCall.Ready
import ComplexityOfGenerators.Simulation.NativeSourceCall.OrdinaryStep
import ComplexityOfGenerators.Simulation.NativeSourceCall.RandomStep

/-! Source execution replay with a fixed linear factor in the selected index.
The source random cursor and output are coupled to their actual native values. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {F O : Type} [Fintype F] [Inhabited F] [Fintype O] (M : Machine Unit Bool O)

theorem replay_next (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (length offset : ℕ) (output : List O)
    (source nextSource : Configuration M) (target : Configuration (machine (F := F) M))
    (ready : Ready M data fixed length offset output source target)
    (next : M.next (generatorData length) (bits.drop offset) source = .running nextSource) :
    ∃ ticks nextTarget, ticks≤4*length+12 ∧
      Ready M data fixed length offset output nextSource nextTarget ∧
      (machine M).Steps data bits target ticks nextTarget := by
  cases sourceTable : M.transition source.state none none
      (if source.indexHead<length then some () else none) (source.work source.workHead) with
  | accept => simp [Machine.next,generatorData,sourceTable] at next
  | reject => simp [Machine.next,generatorData,sourceTable] at next
  | readRandom no yes =>
      cases sourceLookup : (bits.drop offset)[source.randomHead]? with
      | none => simp [Machine.next,generatorData,sourceTable,sourceLookup] at next
      | some bit =>
          simp only [Machine.next,generatorData,List.getElem?_nil,sourceTable,sourceLookup,RunState.running.injEq] at next
          subst nextSource
          have lookup : bits[target.randomHead]?=some bit := by
            rw [ready.random]
            simpa only [List.getElem?_drop] using sourceLookup
          obtain ⟨d,state,path,random,input,auxiliary,index,out⟩ := random_step M data bits fixed source.work
            source.visited length source.indexHead ready.index source.workHead source.state no yes sourceTable target ready.represented bit lookup
          refine ⟨2*source.indexHead+3,d,by have := ready.index; omega,?_,path⟩
          refine ⟨state,ready.index,ready.input,ready.auxiliary,?_,?_,out.trans ready.output⟩
          · exact ⟨ready.geometry.interval,ready.geometry.head,ready.geometry.blank⟩
          · change d.randomHead=offset+(source.randomHead+1)
            rw [random,ready.random]
            omega
  | step state write work input auxiliary index emit =>
      have actualTable : M.transition source.state (generatorData length).input[source.inputHead]?
          (generatorData length).auxiliary[source.auxiliaryHead]?
          (if source.indexHead<(generatorData length).index then some () else none) (source.work source.workHead) =
          .step state write work input auxiliary index emit := by simpa [generatorData] using sourceTable
      rw [M.next_step (generatorData length) (bits.drop offset) source state write work input auxiliary index emit actualTable] at next
      cases next
      obtain ⟨ticks,d,time,newState,path,frame⟩ := ordinary_step M data bits fixed source.work source.visited
        length source.indexHead ready.index source.workHead ready.geometry.head source.state state write work input auxiliary index emit
        sourceTable target ready.represented
      have workMemory : Function.update source.work source.workHead (write.or (source.work source.workHead)) =
          (M.stepConfiguration (generatorData length) source state write work input auxiliary index emit).work := by
        cases write <;> simp [Machine.stepConfiguration,Function.update_eq_self]
      refine ⟨ticks,d,time,?_,path⟩
      refine ⟨?_,index.onInput_le _ _ ready.index,?_,?_,
        M.stepConfiguration_geometry (generatorData length) source ready.geometry state write work input auxiliary index emit,?_,?_⟩
      · simpa only [Machine.stepConfiguration,generatorData,workMemory] using newState
      · change input.onInput 0 source.inputHead=0
        cases input <;> simp [Move.onInput,ready.input]
      · change auxiliary.onInput 0 source.auxiliaryHead=0
        cases auxiliary <;> simp [Move.onInput,ready.auxiliary]
      · exact frame.random.trans ready.random
      · rw [frame.output,ready.output]
        cases emitted : emit <;> simp [Machine.stepConfiguration,emitted,List.append_assoc]

/-- Every source transition costs at most `4*j+12` actual native transitions.
This bound is linear in elapsed source time, even for unbounded work space. -/
theorem replay_steps (data : InputData Unit Bool) (bits : BitString)
    (fixed : ℤ → F) (length offset : ℕ) (output : List O)
    (source nextSource : Configuration M) (target : Configuration (machine (F := F) M))
    (ready : Ready M data fixed length offset output source target) (sourceTicks : ℕ)
    (path : M.Steps (generatorData length) (bits.drop offset) source sourceTicks nextSource) :
    ∃ ticks nextTarget, ticks≤(4*length+12)*sourceTicks ∧
      Ready M data fixed length offset output nextSource nextTarget ∧
      (machine M).Steps data bits target ticks nextTarget := by
  induction path with
  | refl => exact ⟨0,target,by simp,ready,.refl⟩
  | @tail sourceTicks current nextSource sourcePath sourceNext ih =>
      obtain ⟨ticks,currentTarget,time,currentReady,replayed⟩ := ih
      obtain ⟨stepTicks,nextTarget,stepTime,nextReady,nextPath⟩ :=
        replay_next M data bits fixed length offset output current nextSource currentTarget currentReady sourceNext
      refine ⟨ticks+stepTicks,nextTarget,?_,nextReady,replayed.trans (machine M) nextPath⟩
      calc
        ticks+stepTicks ≤ (4*length+12)*sourceTicks+(4*length+12) := Nat.add_le_add time stepTime
        _ = (4*length+12)*(sourceTicks+1) := by rw [Nat.mul_add,Nat.mul_one]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall
