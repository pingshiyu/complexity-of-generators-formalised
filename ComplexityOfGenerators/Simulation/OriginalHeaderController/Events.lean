import ComplexityOfGenerators.Simulation.OriginalHeaderController.Views
import ComplexityOfGenerators.Simulation.WordStack.EventCombinators

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool)

def emitted (tag zero : Bool) (m : Memory (Cell selector) Event 35) : Memory (Cell selector) Event 35 :=
  {m with output:=m.output++[(tag,zero)]}

theorem event_eventReturns (Allowed : Event → ℕ → Prop) (n : ℕ) (bits : BitString)
    (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35)
    (ready : EventReady selector n index m) (allowed : Allowed (tag,decide (index=0)) index) :
    ((event selector tag (decide (index=0))).program 0).EventReturns 0 23 (unitSymbol selector) Allowed n bits
      [((tag,decide (index=0)),index)] m (emitted selector tag (decide (index=0)) m) := by
  let P := (event selector tag (decide (index=0))).program (0 : Fin 35)
  have advance : P.advance n (m.at false) true .stay .stay (some (tag,decide (index=0)))=
      (emitted selector tag (decide (index=0)) m).at true := by
    simp [P,event,Command.program,Program.atom,Program.advance,Memory.at,Configuration.mapState,
      emitted,Action.apply,Move.onInput,Nat.min_eq_left ready.bounded,Function.update_eq_self]
  refine ⟨true,?_,rfl⟩
  refine Program.EventTrace.cons (tag,decide (index=0)) index [] (m.at false) (m.at false) true
    ((emitted selector tag (decide (index=0)) m).at true) 0 (.refl _) rfl allowed rfl ready.selected ready.parameter rfl ?_
  rw [advance]
  exact .nil _ _ 0 (.refl _) rfl

theorem emitIndex_eventReturns (Allowed : Event → ℕ → Prop) (n : ℕ) (bits : BitString)
    (tag : Bool) (index : ℕ) (m : Memory (Cell selector) Event 35)
    (bounded : m.indexHead≤n) (empty : m.store 0=[])
    (parameter : m.store 23=List.replicate index (unitSymbol selector))
    (allowed : Allowed (tag,decide (index=0)) index) :
    ((emitIndex selector tag).program 0).EventReturns 0 23 (unitSymbol selector) Allowed n bits
      [((tag,decide (index=0)),index)] m (afterEvent selector tag index m) := by
  have ready : EventReady selector n index (beforeEvent selector index m) :=
    ⟨bounded,by simpa [beforeEvent,Memory.set] using empty,by simp [beforeEvent]⟩
  cases index with
  | zero =>
      have same : beforeEvent selector 0 m=m := by simp [beforeEvent,←parameter,Memory.set_self]
      have raw := event_eventReturns selector Allowed n bits tag 0 m (same ▸ ready) allowed
      have zeroFlag : decide (0=0)=true := by decide
      rw [zeroFlag] at raw
      change (Program.branch 23 (fun cell input => (cell,input))
        (fun observed => ((if observed.1.isNone then event selector tag true else
          (Routine.ofLocal (Local.pop 23)).command.seq (event selector tag false))).program 0)).EventReturns
        0 23 (unitSymbol selector) Allowed n bits _ m _
      apply Program.EventReturns.branch _ _ _ bounded
      change ((if (m.store (23 : Fin 35)).head?.isNone then event selector tag true else
        (Routine.ofLocal (Local.pop 23)).command.seq (event selector tag false)).program 0).EventReturns
          0 23 (unitSymbol selector) Allowed n bits _ m _
      have head : (m.store (23 : Fin 35)).head?=none := by rw [parameter]; rfl
      rw [head]
      change ((event selector tag true).program 0).EventReturns 0 23 (unitSymbol selector) Allowed n bits
        [((tag,true),0)] m (afterEvent selector tag 0 m)
      simpa [afterEvent,same,emitted] using raw
  | succ index =>
      let middle := beforeEvent selector (index+1) m
      have pop : (Routine.ofLocal (Local.pop 23)).command.Runs n bits m 1 (.done middle) := by
        simpa [middle,beforeEvent,parameter,List.replicate_succ,Routine.ofLocal,Local.pop,Local.command,Command.pop] using
          Command.pop_runs (n:=n) (23 : Fin 35) bits m bounded
      have raw := event_eventReturns selector Allowed n bits tag (index+1) middle ready allowed
      have positiveFlag : decide (index+1=0)=false := by simp
      rw [positiveFlag] at raw
      have annotated := raw.sequence_silent_before (pop.compiled 0 bounded) bounded rfl
      change (Program.branch 23 (fun cell input => (cell,input))
        (fun observed => ((if observed.1.isNone then event selector tag true else
          (Routine.ofLocal (Local.pop 23)).command.seq (event selector tag false))).program 0)).EventReturns
        0 23 (unitSymbol selector) Allowed n bits _ m _
      apply Program.EventReturns.branch _ _ _ bounded
      change ((if (m.store (23 : Fin 35)).head?.isNone then event selector tag true else
        (Routine.ofLocal (Local.pop 23)).command.seq (event selector tag false)).program 0).EventReturns
          0 23 (unitSymbol selector) Allowed n bits _ m _
      have head : (m.store (23 : Fin 35)).head?=some (unitSymbol selector) := by
        rw [parameter,List.replicate_succ]
        rfl
      rw [head]
      change ((Routine.ofLocal (Local.pop 23)).command.program 0).sequence
        ((event selector tag false).program 0) |>.EventReturns 0 23 (unitSymbol selector) Allowed n bits
          [((tag,false),index+1)] m (afterEvent selector tag (index+1) m)
      simpa only [afterEvent,emitted,middle,beforeEvent,Memory.set,positiveFlag] using annotated

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
