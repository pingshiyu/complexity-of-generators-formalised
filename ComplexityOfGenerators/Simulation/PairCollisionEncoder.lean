import ComplexityOfGenerators.Simulation.BinaryOutputDecoder
import ComplexityOfGenerators.Foundations.SpaceBounds
import ComplexityOfGenerators.Foundations.StreamSemanticsProperties

/-! A native linear-time encoder from the paper's three-symbol collision
alphabet to the existing two-bit-block collision encoding. Each source step
uses two target steps; no source coin is changed or consumed twice. -/
namespace ComplexityOfGenerators.Simulation.PairCollisionEncoder
noncomputable section
set_option backward.isDefEq.respectTransparency false
open MeasureTheory
open scoped ENNReal

variable {I A : Type} (M : Machine I A PairSymbol)

def first : PairSymbol → Bool
  | .bit _ => false
  | .separator => true

def second : PairSymbol → Bool
  | .bit b => b
  | .separator => false

def control : (Fin M.states × Option (Option Bool)) ≃
    Fin (Fintype.card (Fin M.states × Option (Option Bool))) := Fintype.equivFin _

def instruction (pending : Option (Option Bool)) (q : Fin M.states) :
    Instruction PairSymbol M.states M.symbols →
      Instruction Bool (Fintype.card (Fin M.states × Option (Option Bool))) M.symbols
  | action => match pending with
    | some emit => .step (control M (q,none)) none .stay .stay .stay .stay emit
    | none => match action with
      | .accept => .accept
      | .reject => .reject
      | .readRandom no yes => .readRandom (control M (no,some none)) (control M (yes,some none))
      | .step next write work input auxiliary index emit =>
          .step (control M (next,some (emit.map second))) write work input auxiliary index (emit.map first)

def machine : Machine I A Bool where
  inputFinite := M.inputFinite
  auxiliaryFinite := M.auxiliaryFinite
  outputFinite := inferInstance
  states := Fintype.card (Fin M.states × Option (Option Bool))
  symbols := M.symbols
  initial := control M (M.initial,none)
  transition := fun state input auxiliary index work =>
    let source := (control M).symm state
    instruction M source.2 source.1 (M.transition source.1 input auxiliary index work)

def configuration (c : Configuration M) : Configuration (machine M) where
  state := control M (c.state,none)
  inputHead := c.inputHead
  auxiliaryHead := c.auxiliaryHead
  indexHead := c.indexHead
  randomHead := c.randomHead
  workHead := c.workHead
  work := c.work
  visited := c.visited
  output := binaryPairWord c.output

def outcome : Outcome PairSymbol → Outcome Bool
  | .accepted word => .accepted (binaryPairWord word)
  | .rejected => .rejected
  | .exhausted => .exhausted

def result : RunState M → RunState (machine M)
  | .running c => .running (configuration M c)
  | .halted r => .halted (outcome r)

def Ready (data : InputData I A) (c : Configuration M) : Prop :=
  c.inputHead≤data.input.length ∧ c.auxiliaryHead≤data.auxiliary.length ∧
    c.indexHead≤data.index ∧ c.workHead∈c.visited

theorem ready_next (data : InputData I A) (bits : BitString) (c d : Configuration M)
    (ready : Ready M data c) (next : M.next data bits c=.running d) : Ready M data d := by
  obtain ⟨hi,ha,hn,hv⟩ := ready
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => simp [Machine.next,action] at next
  | reject => simp [Machine.next,action] at next
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next,action,lookup] at next
      | some b =>
          simp only [Machine.next,action,lookup,RunState.running.injEq] at next
          subst d
          exact ⟨hi,ha,hn,hv⟩
  | step q write work input auxiliary index emit =>
      rw [M.next_step data bits c q write work input auxiliary index emit action] at next
      cases next
      exact ⟨input.onInput_le _ _ hi,auxiliary.onInput_le _ _ ha,index.onInput_le _ _ hn,
        Finset.mem_insert_self _ _⟩

theorem observe (data : InputData I A) (bits : BitString) (c : Configuration M) :
    (machine M).observe data bits (configuration M c)=result M (M.observe data bits c) := by
  simp only [Machine.observe,machine,configuration,Equiv.symm_apply_apply]
  cases M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => rfl
  | reject => rfl
  | readRandom no yes => split_ifs <;> rfl
  | step q write work input auxiliary index emit => rfl

def pendingConfiguration (c : Configuration M) (emit : Option Bool) (out : BitString) :
    Configuration (machine M) :=
  {configuration M c with state := control M (c.state,some emit),output := out}

theorem pending_observe (data : InputData I A) (bits : BitString) (c : Configuration M)
    (emit : Option Bool) (out : BitString) :
    (machine M).observe data bits (pendingConfiguration M c emit out)=
      .running (pendingConfiguration M c emit out) := by
  simp [Machine.observe,machine,pendingConfiguration,configuration,instruction]

theorem pending_next (data : InputData I A) (bits : BitString) (c : Configuration M)
    (ready : Ready M data c) (emit : Option Bool) (out : BitString)
    (output : out++emit.toList=binaryPairWord c.output) :
    (machine M).next data bits (pendingConfiguration M c emit out)=.running (configuration M c) := by
  obtain ⟨hi,ha,hn,hv⟩ := ready
  cases emit <;>
    simp [Machine.next,machine,pendingConfiguration,configuration,instruction,Move.onInput,Move.onInt,
      Nat.min_eq_left hi,Nat.min_eq_left ha,Nat.min_eq_left hn,Finset.insert_eq_of_mem hv] at output ⊢ <;>
    exact output

theorem pending_run (data : InputData I A) (bits : BitString) (c : Configuration M)
    (ready : Ready M data c) (emit : Option Bool) (out : BitString)
    (output : out++emit.toList=binaryPairWord c.output) :
    (machine M).runFrom data bits (pendingConfiguration M c emit out) 1=
      (machine M).observe data bits (configuration M c) := by
  simp only [Machine.runFrom,pending_observe,pending_next M data bits c ready emit out output]

theorem two_steps (data : InputData I A) (bits : BitString) (c d : Configuration M)
    (ready : Ready M data c) (live : M.observe data bits c=.running c)
    (next : M.next data bits c=.running d) :
    (machine M).runFrom data bits (configuration M c) 2=
      (machine M).observe data bits (configuration M d) := by
  have readyD := ready_next M data bits c d ready next
  have normalLive : (machine M).observe data bits (configuration M c)=.running (configuration M c) := by
    rw [observe,live]; rfl
  cases action : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead<data.index then some () else none) (c.work c.workHead) with
  | accept => simp [Machine.observe,action] at live
  | reject => simp [Machine.observe,action] at live
  | readRandom no yes =>
      cases lookup : bits[c.randomHead]? with
      | none => simp [Machine.next,action,lookup] at next
      | some b =>
          simp only [Machine.next,action,lookup,RunState.running.injEq] at next
          subst d
          have targetNext : (machine M).next data bits (configuration M c)=
              .running (pendingConfiguration M ({c with state := (if b then yes else no), randomHead := c.randomHead+1} : Configuration M) none (binaryPairWord c.output)) := by
            cases b <;> simp [Machine.next,machine,configuration,instruction,action,lookup,pendingConfiguration]
          rw [(machine M).runFrom_shift data bits _ _ normalLive targetNext 1]
          apply pending_run M data bits _ readyD none (binaryPairWord c.output)
          simp
  | step q write work input auxiliary index emit =>
      rw [M.next_step data bits c q write work input auxiliary index emit action] at next
      cases next
      have targetNext : (machine M).next data bits (configuration M c)=
          .running (pendingConfiguration M (M.stepConfiguration data c q write work input auxiliary index emit)
            (emit.map second) (binaryPairWord c.output++(emit.map first).toList)) := by
        cases emit <;> cases write <;>
          simp [Machine.next,machine,configuration,instruction,action,pendingConfiguration,Machine.stepConfiguration]
      rw [(machine M).runFrom_shift data bits _ _ normalLive targetNext 1]
      apply pending_run M data bits _ readyD (emit.map second) (binaryPairWord c.output++(emit.map first).toList)
      cases emit with
      | none => simp [Machine.stepConfiguration]
      | some symbol =>
          cases symbol <;> simp [Machine.stepConfiguration,binaryPairWord,pairSymbolBits,first,second,
            List.flatMap_append,List.append_assoc]

theorem runFrom (data : InputData I A) (bits : BitString) (c : Configuration M)
    (ready : Ready M data c) (t : ℕ) :
    (machine M).runFrom data bits (configuration M c) (2*t)=
      result M (M.runFrom data bits c t) := by
  induction t generalizing c with
  | zero => exact observe M data bits c
  | succ t ih =>
      cases observation : M.observe data bits c with
      | halted terminal =>
          have encoded : (machine M).observe data bits (configuration M c)=.halted (outcome terminal) := by
            rw [observe,observation]; rfl
          rw [(machine M).runFrom_halted data bits _ _ encoded,
            M.runFrom_halted data bits c terminal observation]
          rfl
      | running d =>
          have same := M.observe_running_eq data bits c d observation
          subst d
          obtain ⟨d,next⟩ := M.next_running_of_observe_running data bits c observation
          have shifted := (machine M).runFrom_add data bits (configuration M c) (configuration M d) 2
            (two_steps M data bits c d ready observation next) (2*t)
          rw [show 2*(t+1)=2+2*t by omega,shifted,ih d (ready_next M data bits c d ready next),
            M.runFrom_shift data bits c d observation next t]

theorem run (data : InputData I A) (bits : BitString) (t : ℕ) :
    (machine M).run data bits (2*t)=result M (M.run data bits t) := by
  simpa only [show configuration M M.initialConfiguration=(machine M).initialConfiguration from rfl,Machine.runFrom_initial] using runFrom M data bits M.initialConfiguration
    (by simp [Ready,Machine.initialConfiguration]) t

end
end ComplexityOfGenerators.Simulation.PairCollisionEncoder
