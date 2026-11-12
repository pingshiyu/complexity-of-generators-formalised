import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Tail
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Exhausted

/-! Every finite seed either supplies a complete list of actual accepting source
records or genuinely exhausts the hooked native machine. This uses only finite
halting of the original sources and a finite deterministic controller tail. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem finite_tail (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString)
    (events : List (E×ℕ)) (source finishSource : Configuration C)
    (target : Configuration (machine C M parameter start)) (origin : Bool)
    (ready : ControllerReady C M parameter start data origin source target)
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (halting : ∀ entry∈events,(selectedSource M start entry.1).HaltingTransducer (generatorData entry.2)) :
    (∃ records,SourceCalls M start bits source.randomHead events records) ∨
      ∃ ticks,(machine C M parameter start).runFrom data bits target ticks=.halted .exhausted := by
  induction events generalizing source finishSource target origin with
  | nil => exact Or.inl ⟨[],trivial⟩
  | cons entry events ih =>
      cases trace with
      | cons event index _parts _source before resume write _finish segmentTicks segment silent allowed atOrigin action unary rest =>
          obtain ⟨restTicks,restPath⟩ := rest.steps
          have monotoneBefore := segment.randomHead_mono C
          have monotoneAfter := restPath.randomHead_mono C
          have beforeCursor : before.randomHead=source.randomHead := by
            change before.randomHead≤finishSource.randomHead at monotoneAfter
            omega
          have restStable : finishSource.randomHead=
              (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)).randomHead := by
            change finishSource.randomHead=before.randomHead
            omega
          obtain ⟨beforeTarget,beforeReady,beforePath,beforeOutput⟩ := controller_path C M parameter start data bits origin
            source before target ready segmentTicks segment silent
          have sourceHalting := halting (event,index) (by simp)
          obtain ⟨clock,result,run⟩ := sourceHalting.1 (bits.drop before.randomHead)
          obtain ⟨elapsed,within,finishCall,path,observation⟩ := (selectedSource M start event).runFrom_path
            (generatorData index) (bits.drop before.randomHead) (selectedSource M start event).initialConfiguration clock
          have terminal : (selectedSource M start event).observe (generatorData index) (bits.drop before.randomHead) finishCall=.halted result := by
            rw [←observation,Machine.runFrom_initial,run]
          cases result with
          | rejected => exact False.elim (sourceHalting.2 _ clock run)
          | exhausted =>
              obtain ⟨callTicks,time,exhausted⟩ := controller_event_exhausted C M parameter start data bits origin
                before beforeTarget beforeReady resume write event index atOrigin action unary elapsed finishCall path terminal
              refine Or.inr ⟨segmentTicks+callTicks,?_⟩
              rw [(machine C M parameter start).runFrom_add data bits target beforeTarget segmentTicks
                (beforePath.runFrom (machine C M parameter start)),exhausted]
          | accepted word =>
              obtain ⟨callTicks,afterTarget,time,afterReady,callPath,output⟩ := controller_event_accepted C M parameter start data bits origin
                before beforeTarget beforeReady resume write event index atOrigin action unary elapsed finishCall path word terminal
              let record : CallRecord O := ⟨word,elapsed,finishCall.randomHead⟩
              let nextCursor := before.randomHead+finishCall.randomHead
              have rebasedTrace := rest.rebase_random restStable bits nextCursor
              have nextHalting : ∀ entry∈events,(selectedSource M start entry.1).HaltingTransducer (generatorData entry.2) := by
                intro entry member
                exact halting entry (by simp [member])
              have nextReady : ControllerReady C M parameter start data true
                  (C.rebaseRandom (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) nextCursor) afterTarget := afterReady
              have recursive := ih
                (source:=C.rebaseRandom (C.stepConfiguration data before resume write .stay .stay .stay .stay (some event)) nextCursor)
                (finishSource:=C.rebaseRandom finishSource nextCursor) (target:=afterTarget) (origin:=true)
                nextReady rebasedTrace rfl nextHalting
              cases recursive with
              | inl completed =>
                  obtain ⟨records,remainingCalls⟩ := completed
                  refine Or.inl ⟨record::records,?_,?_⟩
                  · refine ⟨finishCall,?_,?_,rfl⟩
                    · simpa only [beforeCursor,record] using path
                    · simpa only [beforeCursor,record] using terminal
                  · simpa only [Machine.rebaseRandom,nextCursor,beforeCursor,record] using remainingCalls
              | inr exhausted =>
                  obtain ⟨remainingTicks,run⟩ := exhausted
                  have prefixPath := beforePath.trans (machine C M parameter start) callPath
                  refine Or.inr ⟨segmentTicks+callTicks+remainingTicks,?_⟩
                  rw [(machine C M parameter start).runFrom_add data bits target afterTarget (segmentTicks+callTicks)
                    (prefixPath.runFrom (machine C M parameter start)),run]

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
