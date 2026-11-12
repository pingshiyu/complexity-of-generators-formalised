import ComplexityOfGenerators.Simulation.OriginalHeaderController.Calls
import ComplexityOfGenerators.Simulation.OriginalHeaderController.CallsBounds

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] parse
variable (selector : Machine Unit Bool Bool)

theorem factorCall_runs (n : ℕ) (bits : BitString) (tag : Bool) (index : ℕ)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (parameter : (parse selector tag).eval m.store 23=List.replicate index (unitSymbol selector))
    (budget : ℕ) (sizes : StoreBound m.store budget) :
    ∃ ticks≤10*budget+10, (factorCall selector tag).Runs n bits m ticks (.done (factorFinished selector tag index m)) ∧
      StoreBound (factorFinished selector tag index m).store budget := by
  obtain ⟨first,firstBound,firstRun⟩ := (parse selector tag).runs bits m bounded
  have parsedEmpty : (parsed selector tag m).store 0=[] :=
    (parse_frame selector tag m.store 0 (by decide) (by decide)).trans empty
  obtain ⟨last,lastBound,lastRun,_⟩ := emitIndex_runs selector n bits tag index (parsed selector tag m)
    bounded parsedEmpty parameter
  have resource := parse_bound selector tag m.store budget sizes
  have cost : first≤10*budget+5 := firstBound.trans resource.2
  exact ⟨first+1+last,by omega,Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun,
    afterEvent_bound selector tag index (parsed selector tag m) budget resource.1 parameter⟩

theorem unionCalls_runs (n : ℕ) (bits : BitString) (tag : Bool)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (master : (m.store 13).length=n) (header : m.store 31=unionHeader selector n tag)
    (budget : ℕ) (sizes : StoreBound m.store budget) :
    ∃ ticks≤20*budget+9,(unionCalls selector).Runs n bits m ticks (.done (unionFinished selector tag n m)) ∧
      StoreBound (unionFinished selector tag n m).store budget := by
  let assign : Controller selector := Routine.assign (O:=Event) 13 23 33 (by decide) (by decide) (by decide) (fun _=>unitSymbol selector)
  have parameter : (unionPrepared selector m).store 23=List.replicate n (unitSymbol selector) := by
    simp [unionPrepared,Routine.assign_eval,List.map_const',master]
  have preparedEmpty : (unionPrepared selector m).store 0=[] := by
    simpa [unionPrepared,Routine.assign_eval] using empty
  obtain ⟨first,firstBound,firstRun⟩ := assign.runs bits m bounded
  obtain ⟨last,lastBound,lastRun,_⟩ := emitIndex_runs selector n bits tag n (unionPrepared selector m)
    bounded preparedEmpty parameter
  have resource := assign_index_bound selector (fun _=>unitSymbol selector) m.store budget sizes
  have cost : first≤20*budget+3 := firstBound.trans resource.2
  have sequence := Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun
  have selected : ((m.store (31 : Fin 35)).head?.bind (headerBit selector)).getD false=tag := by
    rw [header,unionHeader,List.replicate_succ]
    rfl
  refine ⟨1+(first+1+last),by omega,?_,afterEvent_bound selector tag n (unionPrepared selector m) budget resource.1 parameter⟩
  unfold unionCalls
  apply Command.Runs.branch m 31 _ (first+1+last)
  change (assign.command.seq (emitIndex selector (((m.store 31).head?.bind (headerBit selector)).getD false))).Runs _ _ _ _ _
  rw [selected]
  exact sequence

theorem concatenationCalls_runs (n left right : ℕ) (bits : BitString)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (header : m.store 31=concatHeader selector left right) (budget : ℕ) (sizes : StoreBound m.store budget) :
    ∃ ticks≤20*budget+21,(calls selector .concatenation).Runs n bits m ticks
      (.done (factorFinished selector true right (factorFinished selector false left m))) ∧
      StoreBound (factorFinished selector true right (factorFinished selector false left m)).store budget := by
  have leftShape := parse_left selector left right m.store header
  have leftParameter : (parse selector false).eval m.store 23=List.replicate left (unitSymbol selector) := by
    rw [leftShape]; simp
  obtain ⟨first,firstBound,firstRun,firstSizes⟩ := factorCall_runs selector n bits false left m bounded empty leftParameter budget sizes
  let middle := factorFinished selector false left m
  have middleEmpty : middle.store 0=[] :=
    (factorFinished_frame selector false left m 0 (by decide) (by decide)).trans empty
  have middleHeader : middle.store 31=List.replicate (right+1) (Symbol.letter true) := by
    simp [middle,factorFinished,afterEvent,beforeEvent,parsed,Memory.set,leftShape]
  have rightShape := parse_right selector right middle.store middleHeader
  have rightParameter : (parse selector true).eval middle.store 23=List.replicate right (unitSymbol selector) := by
    rw [rightShape]; simp
  obtain ⟨last,lastBound,lastRun,lastSizes⟩ := factorCall_runs selector n bits true right middle bounded middleEmpty rightParameter budget firstSizes
  exact ⟨first+1+last,by omega,Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun,lastSizes⟩

theorem events_runs (operation : Operation) (n : ℕ) (bits : BitString)
    (header : List Bool) (requests : List Request) (choice : Choice operation n header requests)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n)
    (master : (m.store 13).length=n) (payload : m.store 31=header.map Symbol.letter)
    (budget : ℕ) (sizes : StoreBound m.store budget) :
    ∃ ticks≤100*(budget+1),∃next,(events selector operation).Runs n bits m ticks (.done next) ∧
      next.indexHead=m.indexHead ∧ next.randomHead=m.randomHead ∧
      next.output=m.output++(eventList requests).map Prod.fst ∧ StoreBound next.store budget := by
  let clean := m.set 0 []
  have cleanEmpty : clean.store 0=[] := by simp [clean,Memory.set]
  have cleanSizes : StoreBound clean.store budget := sizes.clear 0
  obtain ⟨first,firstBound,firstRun⟩ := (Routine.clear (O:=Event) (0 : Fin 35)).runs bits m bounded
  have firstCost : first≤3*budget+1 := by
    have size := sizes 0
    change first≤3*budget+1
    change first≤3*(m.store 0).length at firstBound
    omega
  cases operation with
  | union =>
    obtain ⟨tag,rfl,rfl⟩ := choice
    have typed : clean.store 31=unionHeader selector n tag := by
      simpa [clean,Memory.set,unionHeader] using payload
    obtain ⟨last,lastBound,lastRun,lastSizes⟩ := unionCalls_runs selector n bits tag clean bounded cleanEmpty
      (by simpa [clean,Memory.set] using master) typed budget cleanSizes
    refine ⟨first+1+last,by omega,unionFinished selector tag n clean,
      Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun,rfl,rfl,?_,lastSizes⟩
    simp [unionFinished,afterEvent,beforeEvent,unionPrepared,clean,Memory.set,eventList]
  | concatenation =>
    obtain ⟨left,leftBound,rfl,rfl⟩ := choice
    have typed : clean.store 31=concatHeader selector left (n-left) := by
      simpa [clean,Memory.set,concatHeader,List.map_append] using payload
    obtain ⟨last,lastBound,lastRun,lastSizes⟩ := concatenationCalls_runs selector n left (n-left) bits clean
      bounded cleanEmpty typed budget cleanSizes
    refine ⟨first+1+last,by omega,factorFinished selector true (n-left) (factorFinished selector false left clean),
      Command.Runs.seq _ _ _ _ _ _ _ firstRun lastRun,?_,?_,?_,lastSizes⟩
    · exact (factorFinished_indexHead selector true (n-left) _).trans
        ((factorFinished_indexHead selector false left clean).trans rfl)
    · exact (factorFinished_randomHead selector true (n-left) _).trans
        ((factorFinished_randomHead selector false left clean).trans rfl)
    · simp only [factorFinished_output,clean,Memory.set,eventList,List.map_cons,List.map_nil,List.append_assoc]
      rfl

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
