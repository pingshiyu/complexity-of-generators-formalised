import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.TailResults

/-! Shared native pipeline for a bounded certification prefix followed by a
stable event tail. This is used by union, concatenation and star frontends. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem prefix_exhausted (data : InputData Unit Bool) (bits : BitString) (ticks : ℕ) (last : Configuration C)
    (prefixPath : C.Steps data bits C.initialConfiguration ticks last)
    (empty : last.output=[]) (exhausted : C.observe data bits last=.halted .exhausted) :
    (machine C M parameter start).run data bits ticks=.halted .exhausted := by
  have ready := initial_controllerReady C M parameter start data
  obtain ⟨target,targetReady,path,output⟩ := controller_path C M parameter start data bits false C.initialConfiguration last
    (machine C M parameter start).initialConfiguration ready ticks prefixPath (by simpa only [Machine.initialConfiguration] using empty)
  have terminal := controller_exhausted_of_observe C M parameter start data bits false last target targetReady exhausted
  rw [←Machine.runFrom_initial,path.runFrom,terminal]

theorem prefix_tail_accept (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString) (outer : ℕ)
    (events : List (E×ℕ)) (bounded : ∀ entry∈events,entry.2≤outer) (records : List (CallRecord O))
    (prefixTicks tailTicks : ℕ) (source finishSource : Configuration C)
    (prefixPath : C.Steps data bits C.initialConfiguration prefixTicks source) (empty : source.output=[])
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (reference : C.Steps data bits source tailTicks finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (calls : SourceCalls M start bits source.randomHead events records)
    (acceptedEvents : List E) (accepted : C.observe data bits finishSource=.halted (.accepted acceptedEvents)) :
    ∃ ticks, ticks≤prefixTicks+tailTicks+(6*outer+20)*(totalTime records+records.length) ∧
      (machine C M parameter start).run data bits ticks=.halted (.accepted (words records)) := by
  have ready := initial_controllerReady C M parameter start data
  obtain ⟨target,targetReady,path,output⟩ := controller_path C M parameter start data bits false C.initialConfiguration source
    (machine C M parameter start).initialConfiguration ready prefixTicks prefixPath (by simpa only [Machine.initialConfiguration] using empty)
  have accepting := accepting_of_observe C data bits finishSource acceptedEvents accepted
  obtain ⟨controllerTicks,ticks,controllerPath,time,run⟩ := execute_tail_accept C M parameter start Allowed data bits outer
    events bounded records source finishSource target false targetReady trace stable calls accepting
  have controllerBound := controllerPath.le_terminal C reference accepted
  refine ⟨prefixTicks+ticks,by omega,?_⟩
  rw [←Machine.runFrom_initial,(machine C M parameter start).runFrom_add data bits _ target prefixTicks
    (path.runFrom (machine C M parameter start)),run,output]
  simp only [Machine.initialConfiguration,List.nil_append]

theorem prefix_tail_halts (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString) (outer : ℕ)
    (events : List (E×ℕ)) (bounded : ∀ entry∈events,entry.2≤outer)
    (prefixTicks : ℕ) (source finishSource : Configuration C)
    (prefixPath : C.Steps data bits C.initialConfiguration prefixTicks source) (empty : source.output=[])
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (halting : ∀ entry∈events,(selectedSource M start entry.1).HaltingTransducer (generatorData entry.2))
    (acceptedEvents : List E) (accepted : C.observe data bits finishSource=.halted (.accepted acceptedEvents)) :
    ∃ ticks result,(machine C M parameter start).run data bits ticks=.halted result ∧ result≠.rejected := by
  have ready := initial_controllerReady C M parameter start data
  obtain ⟨target,targetReady,path,output⟩ := controller_path C M parameter start data bits false C.initialConfiguration source
    (machine C M parameter start).initialConfiguration ready prefixTicks prefixPath (by simpa only [Machine.initialConfiguration] using empty)
  have accepting := accepting_of_observe C data bits finishSource acceptedEvents accepted
  obtain ⟨ticks,result,run,noReject⟩ := tail_halts C M parameter start Allowed data bits outer events bounded source finishSource
    target false targetReady trace stable halting accepting
  refine ⟨prefixTicks+ticks,result,?_,noReject⟩
  rw [←Machine.runFrom_initial,(machine C M parameter start).runFrom_add data bits _ target prefixTicks
    (path.runFrom (machine C M parameter start)),run]

theorem prefix_tail_accepted_iff (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString) (outer : ℕ)
    (events : List (E×ℕ)) (bounded : ∀ entry∈events,entry.2≤outer)
    (prefixTicks tailTicks : ℕ) (source finishSource : Configuration C)
    (prefixPath : C.Steps data bits C.initialConfiguration prefixTicks source) (empty : source.output=[])
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (reference : C.Steps data bits source tailTicks finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (halting : ∀ entry∈events,(selectedSource M start entry.1).HaltingTransducer (generatorData entry.2))
    (acceptedEvents : List E) (accepted : C.observe data bits finishSource=.halted (.accepted acceptedEvents)) (word : List O) :
    (∃ ticks,(machine C M parameter start).run data bits ticks=.halted (.accepted word)) ↔
      ∃ records,SourceCalls M start bits source.randomHead events records ∧ word=words records := by
  have ready := initial_controllerReady C M parameter start data
  obtain ⟨target,targetReady,path,output⟩ := controller_path C M parameter start data bits false C.initialConfiguration source
    (machine C M parameter start).initialConfiguration ready prefixTicks prefixPath (by simpa only [Machine.initialConfiguration] using empty)
  constructor
  · rintro ⟨givenTicks,given⟩
    cases finite_tail C M parameter start Allowed data bits events source finishSource target false targetReady trace stable halting with
    | inr exhausted =>
        obtain ⟨ticks,run⟩ := exhausted
        have exhaustedRun : (machine C M parameter start).run data bits (prefixTicks+ticks)=.halted .exhausted := by
          rw [←Machine.runFrom_initial,(machine C M parameter start).runFrom_add data bits _ target prefixTicks
            (path.runFrom (machine C M parameter start)),run]
        have impossible := (machine C M parameter start).halted_outcome_unique data bits givenTicks (prefixTicks+ticks) _ _ given exhaustedRun
        cases impossible
    | inl completed =>
        obtain ⟨records,calls⟩ := completed
        obtain ⟨ticks,time,run⟩ := prefix_tail_accept C M parameter start Allowed data bits outer events bounded records prefixTicks tailTicks
          source finishSource prefixPath empty trace reference stable calls acceptedEvents accepted
        have same := (machine C M parameter start).halted_outcome_unique data bits givenTicks ticks _ _ given run
        exact ⟨records,calls,Outcome.accepted.inj same⟩
  · rintro ⟨records,calls,equal⟩
    obtain ⟨ticks,time,run⟩ := prefix_tail_accept C M parameter start Allowed data bits outer events bounded records prefixTicks tailTicks
      source finishSource prefixPath empty trace reference stable calls acceptedEvents accepted
    exact ⟨ticks,by simpa only [equal] using run⟩

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
