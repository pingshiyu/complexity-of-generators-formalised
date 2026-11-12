import ComplexityOfGenerators.Simulation.OriginalHeaderController.Calls

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] parse
variable (selector : Machine Unit Bool Bool)

theorem events_eventReturns (operation : Operation) (n : ℕ) (bits : BitString)
    (header : List Bool) (requests : List Request) (choice : Choice operation n header requests)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n)
    (master : (m.store 13).length=n) (payload : m.store 31=header.map Symbol.letter) :
    ∃ next, ((events selector operation).program 0).EventReturns 0 23 (unitSymbol selector) allowed n bits
        (eventList requests) m next ∧
      next.indexHead=m.indexHead ∧ next.randomHead=m.randomHead ∧
      next.output=m.output++(eventList requests).map Prod.fst := by
  let clean := m.set 0 []
  have cleanBound : clean.indexHead≤n := bounded
  have cleanEmpty : clean.store 0=[] := by simp [clean,Memory.set]
  have cleanMaster : (clean.store 13).length=n := by simpa [clean,Memory.set] using master
  obtain ⟨ticks,_,clearRun⟩ := (Routine.clear (O:=Event) (0 : Fin 35)).runs bits m bounded
  have clearReturns := clearRun.compiled 0 bounded
  cases operation with
  | union =>
    obtain ⟨tag,rfl,rfl⟩ := choice
    have typed : clean.store 31=unionHeader selector n tag := by
      simpa [clean,Memory.set,unionHeader] using payload
    have raw := unionCalls_eventReturns selector allowed n bits tag clean cleanBound cleanEmpty cleanMaster typed rfl
    refine ⟨unionFinished selector tag n clean,?_,rfl,rfl,?_⟩
    · exact raw.sequence_silent_before clearReturns bounded rfl
    · simp [unionFinished,afterEvent,beforeEvent,unionPrepared,clean,Memory.set,eventList]
  | concatenation =>
    obtain ⟨left,leftBound,rfl,rfl⟩ := choice
    have typed : clean.store 31=concatHeader selector left (n-left) := by
      simpa [clean,Memory.set,concatHeader,List.map_append] using payload
    have raw := concatenationCalls_eventReturns selector allowed n left (n-left) bits clean cleanBound cleanEmpty typed rfl rfl
    refine ⟨factorFinished selector true (n-left) (factorFinished selector false left clean),?_,?_,?_,?_⟩
    · exact raw.sequence_silent_before clearReturns bounded rfl
    · exact (factorFinished_indexHead selector true (n-left) _).trans
        ((factorFinished_indexHead selector false left clean).trans rfl)
    · exact (factorFinished_randomHead selector true (n-left) _).trans
        ((factorFinished_randomHead selector false left clean).trans rfl)
    · simp only [factorFinished_output,clean,Memory.set,eventList,List.map_cons,List.map_nil,List.append_assoc]
      rfl

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
