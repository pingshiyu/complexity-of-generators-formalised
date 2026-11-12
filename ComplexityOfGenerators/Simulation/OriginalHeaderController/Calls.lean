import ComplexityOfGenerators.Simulation.OriginalHeaderController.Events
import ComplexityOfGenerators.Simulation.OriginalHeaderController.Choice

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool)

def parsed (tag : Bool) (m : Memory (Cell selector) Event 35) : Memory (Cell selector) Event 35 :=
  {m with store:=(parse selector tag).eval m.store}
def factorFinished (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35) : Memory (Cell selector) Event 35 :=
  afterEvent selector tag index (parsed selector tag m)
def unionPrepared (m : Memory (Cell selector) Event 35) : Memory (Cell selector) Event 35 :=
  {m with store:=(Routine.assign (O := Event) 13 23 33 (by decide) (by decide) (by decide)
    (fun _ => unitSymbol selector)).eval m.store}
def unionFinished (tag : Bool) (n : ℕ) (m : Memory (Cell selector) Event 35) : Memory (Cell selector) Event 35 :=
  afterEvent selector tag n (unionPrepared selector m)

@[simp] theorem factorFinished_indexHead (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35) :
    (factorFinished selector tag index m).indexHead=m.indexHead := rfl
@[simp] theorem factorFinished_randomHead (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35) :
    (factorFinished selector tag index m).randomHead=m.randomHead := rfl
@[simp] theorem factorFinished_output (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35) :
    (factorFinished selector tag index m).output=m.output++[(tag,decide (index=0))] := rfl

theorem parse_frame (tag : Bool) (s : Store selector) (reg : Fin 35) (differentExport : reg≠23) (differentHeader : reg≠31) :
    (parse selector tag).eval s reg=s reg := by
  simp [parse,Routine.seq,Routine.clear,Routine.transferWhile,Routine.ofLocal,Local.eval_pop,differentExport,differentHeader]

theorem factorFinished_frame (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35)
    (reg : Fin 35) (differentExport : reg≠23) (differentHeader : reg≠31) :
    (factorFinished selector tag index m).store reg=m.store reg := by
  simpa only [factorFinished,afterEvent,beforeEvent,parsed,Memory.set,Function.update_of_ne differentExport] using
    parse_frame selector tag m.store reg differentExport differentHeader

theorem factorCall_eventReturns (Allowed : Event→ℕ→Prop) (n : ℕ) (bits : BitString) (tag : Bool) (index : ℕ)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (parameter : (parse selector tag).eval m.store 23=List.replicate index (unitSymbol selector))
    (accept : Allowed (tag,decide (index=0)) index) :
    ((factorCall selector tag).program 0).EventReturns 0 23 (unitSymbol selector) Allowed n bits
      [((tag,decide (index=0)),index)] m (factorFinished selector tag index m) := by
  have nextEmpty : (parsed selector tag m).store 0=[] :=
    (parse_frame selector tag m.store 0 (by decide) (by decide)).trans empty
  have raw := emitIndex_eventReturns selector Allowed n bits tag index (parsed selector tag m)
    bounded nextEmpty parameter accept
  obtain ⟨ticks,_,run⟩ := (parse selector tag).runs bits m bounded
  exact raw.sequence_silent_before (run.compiled 0 bounded) bounded rfl

theorem unionCalls_eventReturns (Allowed : Event→ℕ→Prop) (n : ℕ) (bits : BitString) (tag : Bool)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (master : (m.store 13).length=n) (header : m.store 31=unionHeader selector n tag)
    (accept : Allowed (tag,decide (n=0)) n) :
    ((unionCalls selector).program 0).EventReturns 0 23 (unitSymbol selector) Allowed n bits
      [((tag,decide (n=0)),n)] m (unionFinished selector tag n m) := by
  let assign : Controller selector := Routine.assign (S := Cell selector) (O := Event) 13 23 33 (by decide) (by decide) (by decide)
    (fun _ => unitSymbol selector)
  have parameter : (unionPrepared selector m).store 23=List.replicate n (unitSymbol selector) := by
    simp [unionPrepared,Routine.assign_eval,List.map_const',master]
  have preparedEmpty : (unionPrepared selector m).store 0=[] := by
    simpa [unionPrepared,Routine.assign_eval] using empty
  have raw := emitIndex_eventReturns selector Allowed n bits tag n (unionPrepared selector m)
    bounded preparedEmpty parameter accept
  obtain ⟨ticks,_,run⟩ := assign.runs bits m bounded
  have annotated := raw.sequence_silent_before (run.compiled 0 bounded) bounded rfl
  change (Program.branch 31 (fun cell index => (cell,index))
    (fun observed => (assign.command.seq (emitIndex selector ((observed.1.bind (headerBit selector)).getD false))).program 0)).EventReturns
      0 23 (unitSymbol selector) Allowed n bits _ m _
  apply Program.EventReturns.branch _ _ _ bounded
  let chosenTag := ((m.store (31 : Fin 35)).head?.bind (headerBit selector)).getD false
  change ((assign.command.seq (emitIndex selector chosenTag)).program 0).EventReturns
    0 23 (unitSymbol selector) Allowed n bits _ m _
  have head : (m.store (31 : Fin 35)).head?=some (Symbol.letter tag) := by
    rw [header,unionHeader,List.replicate_succ]
    rfl
  have chosen : chosenTag=tag := by
    change ((m.store (31 : Fin 35)).head?.bind (headerBit selector)).getD false=tag
    rw [head]
    rfl
  rw [chosen]
  change (assign.command.program 0 |>.sequence ((emitIndex selector tag).program 0)).EventReturns
    0 23 (unitSymbol selector) Allowed n bits _ m _
  exact annotated

theorem concatenationCalls_eventReturns (Allowed : Event→ℕ→Prop) (n left right : ℕ) (bits : BitString)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (header : m.store 31=concatHeader selector left right)
    (acceptLeft : Allowed (false,decide (left=0)) left) (acceptRight : Allowed (true,decide (right=0)) right) :
    ((calls selector .concatenation).program 0).EventReturns 0 23 (unitSymbol selector) Allowed n bits
      [((false,decide (left=0)),left),((true,decide (right=0)),right)] m
      (factorFinished selector true right (factorFinished selector false left m)) := by
  have leftShape := parse_left selector left right m.store header
  have leftParameter : (parse selector false).eval m.store 23=List.replicate left (unitSymbol selector) := by
    rw [leftShape]
    simp
  have first := factorCall_eventReturns selector Allowed n bits false left m bounded empty leftParameter acceptLeft
  let middle := factorFinished selector false left m
  have nextEmpty : middle.store 0=[] :=
    (factorFinished_frame selector false left m 0 (by decide) (by decide)).trans empty
  have nextHeader : middle.store 31=List.replicate (right+1) (Symbol.letter true) := by
    simp [middle,factorFinished,afterEvent,beforeEvent,parsed,Memory.set,leftShape]
  have rightShape := parse_right selector right middle.store nextHeader
  have rightParameter : (parse selector true).eval middle.store 23=List.replicate right (unitSymbol selector) := by
    rw [rightShape]
    simp
  have second := factorCall_eventReturns selector Allowed n bits true right middle bounded nextEmpty rightParameter acceptRight
  exact first.sequence second bounded

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
