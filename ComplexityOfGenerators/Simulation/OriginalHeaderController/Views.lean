import ComplexityOfGenerators.Simulation.OriginalHeaderController.Basic

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool)

private theorem split_replicates {S : Type} (keep : S → Bool) (a b : S)
    (first : keep a=true) (second : keep b=false) (left right : ℕ) :
    (List.replicate left a++List.replicate right b).takeWhile keep=List.replicate left a ∧
      (List.replicate left a++List.replicate right b).dropWhile keep=List.replicate right b := by
  induction left with
  | zero => cases right <;> simp [List.replicate_succ,second]
  | succ left ih => simpa [List.replicate_succ,first] using ih

@[simp] theorem headerBit_letter (tag : Bool) : headerBit selector (Symbol.letter tag)=some tag := rfl

theorem parse_left (left right : ℕ) (s : Store selector)
    (header : s 31=concatHeader selector left right) :
    (parse selector false).eval s=Function.update (Function.update s 31
      (List.replicate (right+1) (Symbol.letter true))) 23 (List.replicate left (unitSymbol selector)) := by
  have split := split_replicates (fun cell => headerBit selector cell==some false)
    (Symbol.letter false) (Symbol.letter true) (by simp) (by simp) (left+1) (right+1)
  funext reg
  by_cases atSource : reg=31 <;> by_cases atExport : reg=23 <;>
    simp [parse,Routine.seq,Routine.clear,Routine.transferWhile,Routine.ofLocal,Local.eval_pop,
      Function.update_apply,atSource,atExport,header,concatHeader,split.1,split.2,List.map_const',unitSymbol]

theorem parse_right (right : ℕ) (s : Store selector)
    (header : s 31=List.replicate (right+1) (Symbol.letter true)) :
    (parse selector true).eval s=Function.update (Function.update s 31 [])
      23 (List.replicate right (unitSymbol selector)) := by
  have split := split_replicates (fun cell => headerBit selector cell==some true)
    (Symbol.letter true) (Symbol.letter false) (by simp) (by simp) (right+1) 0
  simp only [List.replicate_zero,List.append_nil] at split
  funext reg
  by_cases atSource : reg=31 <;> by_cases atExport : reg=23 <;>
    simp [parse,Routine.seq,Routine.clear,Routine.transferWhile,Routine.ofLocal,Local.eval_pop,
      Function.update_apply,atSource,atExport,header,split.1,split.2,List.map_const',unitSymbol]

structure EventReady (n index : ℕ) (m : Memory (Cell selector) Event 35) : Prop where
  bounded : m.indexHead≤n
  selected : m.store 0=[]
  parameter : m.store 23=List.replicate (index-1) (unitSymbol selector)

def beforeEvent (index : ℕ) (m : Memory (Cell selector) Event 35) : Memory (Cell selector) Event 35 :=
  m.set 23 (List.replicate (index-1) (unitSymbol selector))
def afterEvent (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35) : Memory (Cell selector) Event 35 :=
  {beforeEvent selector index m with output:=m.output++[(tag,decide (index=0))]}

theorem event_runs (n : ℕ) (bits : BitString) (tag zero : Bool)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) :
    (event selector tag zero).Runs n bits m 1 (.done {m with output:=m.output++[(tag,zero)]}) := by
  have run := Command.Runs.act (n:=n) (bits:=bits) m 0 .stay .stay (some (tag,zero))
  simpa [event,Program.changeMemory,Action.apply,Move.onInput,Nat.min_eq_left bounded,Function.update_eq_self] using run

/-- Zero and positive indices issue explicit events at an empty register.
The original index is represented by the event together with `index-1`
export cells, so index-zero calls need no fictitious live unary cell. -/
theorem emitIndex_runs (n : ℕ) (bits : BitString) (tag : Bool) (index : ℕ)
    (m : Memory (Cell selector) Event 35) (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (parameter : m.store 23=List.replicate index (unitSymbol selector)) :
    ∃ ticks≤4,(emitIndex selector tag).Runs n bits m ticks (.done (afterEvent selector tag index m)) ∧
      EventReady selector n index (beforeEvent selector index m) := by
  have ready : EventReady selector n index (beforeEvent selector index m) :=
    ⟨bounded,by simpa [beforeEvent,Memory.set] using empty,by simp [beforeEvent]⟩
  cases index with
  | zero =>
      have same : beforeEvent selector 0 m=m := by simp [beforeEvent,←parameter,Memory.set_self]
      refine ⟨2,by decide,?_,ready⟩
      unfold emitIndex
      refine Command.Runs.branch m 23 _ 1 _ ?_
      simpa [observe,parameter,emitIndex,afterEvent,same] using event_runs selector n bits tag true m bounded
  | succ index =>
      let middle := beforeEvent selector (index+1) m
      have pop : (Routine.ofLocal (Local.pop 23)).command.Runs n bits m 1 (.done middle) := by
        simpa [middle,beforeEvent,parameter,List.replicate_succ,Routine.ofLocal,Local.pop,Local.command,Command.pop] using
          Command.pop_runs (n:=n) (23 : Fin 35) bits m (by omega)
      have emit := event_runs selector n bits tag false middle bounded
      have run := Command.Runs.seq _ _ _ _ _ _ _ pop emit
      refine ⟨4,by decide,?_,ready⟩
      unfold emitIndex
      refine Command.Runs.branch m 23 _ 3 _ ?_
      simpa [observe,parameter,emitIndex,afterEvent,middle,beforeEvent] using run

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
