import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.FiniteTail
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Controller.Terminal

/-! Native acceptance, finite halting, and exact output soundness for a finite
deterministic event tail. Source support enters only through actual paths. -/
namespace ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {E O : Type} [Fintype E] [Fintype O] (C : Machine Unit Bool E) (M : Machine Unit Bool O)
    (parameter : E → Fixed C → Bool) (start : E → Fin M.states)

theorem execute_tail_accept (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString) (outer : ℕ)
    (events : List (E×ℕ)) (bounded : ∀ entry∈events,entry.2≤outer) (records : List (CallRecord O))
    (source finishSource : Configuration C) (target : Configuration (machine C M parameter start)) (origin : Bool)
    (ready : ControllerReady C M parameter start data origin source target)
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (calls : SourceCalls M start bits source.randomHead events records)
    (accepting : C.transition finishSource.state data.input[finishSource.inputHead]? data.auxiliary[finishSource.auxiliaryHead]?
      (if finishSource.indexHead<data.index then some () else none) (finishSource.work finishSource.workHead)=.accept) :
    ∃ controllerTicks ticks, C.Steps data bits source controllerTicks finishSource ∧
      ticks≤controllerTicks+(6*outer+20)*(totalTime records+records.length) ∧
      (machine C M parameter start).runFrom data bits target ticks=.halted (.accepted (target.output++words records)) := by
  obtain ⟨controllerTicks,ticks,lastOrigin,last,controllerPath,time,lastReady,path,output⟩ :=
    execute_tail C M parameter start Allowed data bits outer events bounded records source finishSource target origin ready trace stable calls
  have terminal := controller_accept C M parameter start data bits lastOrigin
    (C.rebaseRandom finishSource (source.randomHead+totalCoins records)) last lastReady accepting
  refine ⟨controllerTicks,ticks,controllerPath,time,?_⟩
  rw [path.runFrom (machine C M parameter start),terminal,output]

theorem tail_halts (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString) (outer : ℕ)
    (events : List (E×ℕ)) (bounded : ∀ entry∈events,entry.2≤outer)
    (source finishSource : Configuration C) (target : Configuration (machine C M parameter start)) (origin : Bool)
    (ready : ControllerReady C M parameter start data origin source target)
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (halting : ∀ entry∈events,(selectedSource M start entry.1).HaltingTransducer (generatorData entry.2))
    (accepting : C.transition finishSource.state data.input[finishSource.inputHead]? data.auxiliary[finishSource.auxiliaryHead]?
      (if finishSource.indexHead<data.index then some () else none) (finishSource.work finishSource.workHead)=.accept) :
    ∃ ticks result,(machine C M parameter start).runFrom data bits target ticks=.halted result ∧ result≠.rejected := by
  cases finite_tail C M parameter start Allowed data bits events source finishSource target origin ready trace stable halting with
  | inr exhausted => obtain ⟨ticks,run⟩ := exhausted; exact ⟨ticks,.exhausted,run,by simp⟩
  | inl completed =>
      obtain ⟨records,calls⟩ := completed
      obtain ⟨controllerTicks,ticks,path,time,run⟩ := execute_tail_accept C M parameter start Allowed data bits outer events bounded
        records source finishSource target origin ready trace stable calls accepting
      exact ⟨ticks,.accepted (target.output++words records),run,by simp⟩

private theorem outcomes_unique (H : Machine Unit Bool O) (data : InputData Unit Bool) (bits : BitString)
    (c : Configuration H) (t s : ℕ) (first second : Outcome O)
    (left : H.runFrom data bits c t=.halted first) (right : H.runFrom data bits c s=.halted second) : first=second := by
  have a := H.runFrom_halted_add data bits c t first left s
  have b := H.runFrom_halted_add data bits c s second right t
  rw [Nat.add_comm s t] at b
  exact RunState.halted.inj (a.symm.trans b)

theorem tail_accepted_iff (Allowed : E→ℕ→Prop) (data : InputData Unit Bool) (bits : BitString) (outer : ℕ)
    (events : List (E×ℕ)) (bounded : ∀ entry∈events,entry.2≤outer)
    (source finishSource : Configuration C) (target : Configuration (machine C M parameter start)) (origin : Bool)
    (ready : ControllerReady C M parameter start data origin source target)
    (trace : C.NativeEventTrace parameter Allowed data bits events source finishSource)
    (stable : finishSource.randomHead=source.randomHead)
    (halting : ∀ entry∈events,(selectedSource M start entry.1).HaltingTransducer (generatorData entry.2))
    (accepting : C.transition finishSource.state data.input[finishSource.inputHead]? data.auxiliary[finishSource.auxiliaryHead]?
      (if finishSource.indexHead<data.index then some () else none) (finishSource.work finishSource.workHead)=.accept)
    (word : List O) :
    (∃ ticks,(machine C M parameter start).runFrom data bits target ticks=.halted (.accepted word)) ↔
      ∃ records,SourceCalls M start bits source.randomHead events records ∧ word=target.output++words records := by
  constructor
  · rintro ⟨givenTicks,given⟩
    cases finite_tail C M parameter start Allowed data bits events source finishSource target origin ready trace stable halting with
    | inr exhausted =>
        obtain ⟨ticks,run⟩ := exhausted
        have impossible := outcomes_unique (machine C M parameter start) data bits target givenTicks ticks _ _ given run
        cases impossible
    | inl completed =>
        obtain ⟨records,calls⟩ := completed
        obtain ⟨controllerTicks,ticks,path,time,run⟩ := execute_tail_accept C M parameter start Allowed data bits outer events bounded
          records source finishSource target origin ready trace stable calls accepting
        have same := outcomes_unique (machine C M parameter start) data bits target givenTicks ticks _ _ given run
        exact ⟨records,calls,Outcome.accepted.inj same⟩
  · rintro ⟨records,calls,equal⟩
    obtain ⟨controllerTicks,ticks,path,time,run⟩ := execute_tail_accept C M parameter start Allowed data bits outer events bounded
      records source finishSource target origin ready trace stable calls accepting
    exact ⟨ticks,by simpa only [equal] using run⟩

end
end ComplexityOfGenerators.Simulation.NativeSourceCall.Hook
