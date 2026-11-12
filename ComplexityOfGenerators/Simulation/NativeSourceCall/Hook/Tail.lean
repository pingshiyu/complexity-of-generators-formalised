import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Path
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Call
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Records
import ComplexityOfGenerators.Simulation.NativeEventTraceRebase

/-! A deterministic native event tail interleaves actual original-source calls.
After each call the remaining native trace is replayed at the consumed cursor;
source runtimes contribute additively, without a second-moment loss. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem execute_tail (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString) (outer : ℕ)
    (events : List (E×ℕ)) (bounded : ∀ entry∈events,entry.2≤outer) (records : List (CallRecord O))
    (source finishSource : Configuration C) (target : Configuration (machine C M parameter start)) (origin : Bool)
    (ready : ControllerReady C M parameter start data origin source target)
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (calls : SourceCalls M start bits source.randomHead events records) :
    ∃ controllerTicks ticks finalOrigin finishTarget,
      C.Steps data bits source controllerTicks finishSource ∧
      ticks≤controllerTicks+(6*outer+20)*(totalTime records+records.length) ∧
      ControllerReady C M parameter start data finalOrigin
        (C.rebaseRandom finishSource (source.randomHead+totalCoins records)) finishTarget ∧
      (machine C M parameter start).Steps data bits target ticks finishTarget ∧
      finishTarget.output=target.output++words records := by
  induction events generalizing source finishSource records target origin with
  | nil =>
      cases records with
      | cons record records => exact False.elim calls
      | nil =>
          cases trace with
          | nil _source _finish ticks path noEvent =>
              obtain ⟨last,lastReady,replayed,output⟩ := controller_path C M parameter start data bits origin
                source finishSource target ready ticks path noEvent
              refine ⟨ticks,ticks,origin,last,path,by simp [totalTime],?_,replayed,?_⟩
              · have same : C.rebaseRandom finishSource (source.randomHead+totalCoins ([] : List (CallRecord O)))=finishSource := by
                  apply C.rebaseRandom_eq
                  simpa [totalCoins] using stable.symm
                simpa only [same] using lastReady
              · simpa [words] using output
  | cons entry events ih =>
      cases records with
      | nil => exact False.elim calls
      | cons record records =>
          cases trace with
          | cons event index _parts _source before resume write _finish segmentTicks segment silent allowed atOrigin action unary rest =>
              rcases calls with ⟨firstCall,remainingCalls⟩
              obtain ⟨finishCall,sourcePath,sourceAccepted,sourceCursor⟩ := firstCall
              obtain ⟨restClock,restPath⟩ := rest.steps
              have monotoneBefore := segment.randomHead_mono C
              have monotoneAfter := restPath.randomHead_mono C
              have beforeCursor : before.randomHead=source.randomHead := by
                change before.randomHead≤finishSource.randomHead at monotoneAfter
                omega
              have restStable : finishSource.randomHead=
                  (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)).randomHead := by
                change finishSource.randomHead=before.randomHead
                omega
              obtain ⟨beforeTarget,beforeReady,beforePath,beforeOutput⟩ := controller_path C M parameter start
                data bits origin source before target ready segmentTicks segment silent
              have actualSourcePath : (selectedSource M start event).Steps (generatorData index) (bits.drop before.randomHead)
                  (selectedSource M start event).initialConfiguration record.time finishCall := by
                simpa only [beforeCursor] using sourcePath
              have actualAccepted : (selectedSource M start event).observe (generatorData index) (bits.drop before.randomHead) finishCall=.halted (.accepted record.word) := by
                simpa only [beforeCursor] using sourceAccepted
              obtain ⟨callTicks,afterTarget,callTime,afterReady,callPath,callOutput⟩ := controller_event_accepted C M parameter start
                data bits origin before beforeTarget beforeReady resume write event index atOrigin action unary
                record.time finishCall actualSourcePath record.word actualAccepted
              let nextCursor := source.randomHead+record.coins
              have nextReady : ControllerReady C M parameter start data true
                  (C.rebaseRandom (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) nextCursor) afterTarget := by
                simpa only [beforeCursor,sourceCursor,nextCursor] using afterReady
              have rebasedTrace := rest.rebase_random restStable bits nextCursor
              have rebasedCalls : SourceCalls M start bits
                  (C.rebaseRandom (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) nextCursor).randomHead events records := remainingCalls
              have restBound : ∀ entry∈events,entry.2≤outer := by
                intro entry member
                exact bounded entry (by simp [member])
              obtain ⟨remainingController,remainingTicks,lastOrigin,last,controllerRest,remainingTime,lastReady,remainingPath,lastOutput⟩ :=
                ih (bounded:=restBound) (records:=records)
                  (source:=C.rebaseRandom (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) nextCursor)
                  (finishSource:=C.rebaseRandom finishSource nextCursor) (target:=afterTarget) (origin:=true)
                  nextReady rebasedTrace rfl rebasedCalls
              have restoredPath := controllerRest.rebase_random C (by rfl) bits before.randomHead
              have restoreStart : C.rebaseRandom
                  (C.rebaseRandom (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) nextCursor)
                  before.randomHead=C.stepConfiguration data before resume write .stay .stay .stay .stay (some event) := by
                rw [C.rebaseRandom_twice]
                apply C.rebaseRandom_eq
                rfl
              have restoreFinish : C.rebaseRandom (C.rebaseRandom finishSource nextCursor) before.randomHead=finishSource := by
                rw [C.rebaseRandom_twice]
                apply C.rebaseRandom_eq
                exact restStable.symm
              have originalRest : C.Steps data bits
                  (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) remainingController finishSource := by
                simpa only [restoreStart,restoreFinish] using restoredPath
              have eventPath : C.Steps data bits before 1
                  (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) :=
                .tail .refl (C.next_step data bits before resume write .stay .stay .stay .stay (some event) action)
              have indexBound := bounded (event,index) (by simp)
              have callBound : callTicks≤1+(6*outer+20)*(record.time+1) := by
                apply callTime.trans
                exact Nat.add_le_add_left (Nat.mul_le_mul_right (record.time+1) (by omega)) 1
              refine ⟨segmentTicks+1+remainingController,segmentTicks+callTicks+remainingTicks,lastOrigin,last,
                (segment.trans C eventPath).trans C originalRest,?_,?_,
                (beforePath.trans (machine C M parameter start) callPath).trans (machine C M parameter start) remainingPath,?_⟩
              · calc
                  segmentTicks+callTicks+remainingTicks ≤ segmentTicks+(1+(6*outer+20)*(record.time+1))+
                    (remainingController+(6*outer+20)*(totalTime records+records.length)) := by omega
                  _ = segmentTicks+1+remainingController+(6*outer+20)*(totalTime (record::records)+(record::records).length) := by
                    simp only [totalTime,List.map_cons,List.sum_cons,List.length_cons,Nat.mul_add,Nat.mul_one]
                    omega
              · have cursor : nextCursor+totalCoins records=source.randomHead+totalCoins (record::records) := by
                  simp only [nextCursor,totalCoins,List.map_cons,List.sum_cons]
                  omega
                simpa only [Machine.rebaseRandom_twice,cursor,Machine.rebaseRandom] using lastReady
              · rw [lastOutput,callOutput,beforeOutput]
                simp [words,List.append_assoc]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
