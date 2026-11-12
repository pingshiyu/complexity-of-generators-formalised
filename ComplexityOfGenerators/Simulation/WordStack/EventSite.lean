import ComplexityOfGenerators.Simulation.WordStack.PathCompilation
import ComplexityOfGenerators.Simulation.TransducerBank.OriginEvent

namespace ComplexityOfGenerators.Simulation.WordStack.Program
open TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {Q S E : Type} {k : ℕ} [Fintype Q] [Fintype S] [Fintype E]
    (P : Program Q S E k)

theorem event_site (n : ℕ) (bits : BitString) (before : Configuration Q S E k)
    (next : Q) (e : E) (r : ℕ) (negative : Fin k→Bool)
    (start : ComplexityOfGenerators.Configuration P.machine)
    (ready : BankReady P.bank (P.encoded before) negative start)
    (bounded : P.bank.Bounded (generatorData n) r (P.encoded before))
    (empty : before.store (P.select before.state)=[])
    (table : P.instruction n before=.step next .stay .stay (some e)) :
    ∃ q write,
      P.machine.transition start.state (generatorData n).input[start.inputHead]?
        (generatorData n).auxiliary[start.auxiliaryHead]?
        (if start.indexHead<n then some () else none) (start.work start.workHead)=
          .step q write .stay .stay .stay .stay (some e) ∧
      BankMemory P.bank (fun i=>tape (before.store i))
        (Function.update (fun i=>some ((P.encoded before).head i)) (P.select before.state) none)
        (P.machine.stepConfiguration (generatorData n) start q write .stay .stay .stay .stay (some e)).work ∧
      ∃ ticks target sides,
        BankReady P.bank (P.encoded (P.advance n before next .stay .stay (some e))) sides target ∧
        P.machine.Steps (generatorData n) bits
          (P.machine.stepConfiguration (generatorData n) start q write .stay .stay .stay .stay (some e)) ticks target ∧
        target.output=(P.machine.stepConfiguration (generatorData n) start q write .stay .stay .stay .stay (some e)).output := by
  let source := P.encoded before
  let j := P.select before.state
  let symbol := (before.store j).head?
  have selectedBank : P.bank.select source.state=j := rfl
  have origin : source.head (P.bank.select source.state)=0 := by
    rw [selectedBank]
    change ((before.store j).length : ℤ)=0
    rw [show before.store j=[] from empty]
    rfl
  have bankTable := P.encoded_instruction n before
  rw [table] at bankTable
  let q := eventNext P.bank start negative j (.ready next)
  let write := eventWrite P.bank start j symbol
  have action : P.machine.transition start.state (generatorData n).input[start.inputHead]?
      (generatorData n).auxiliary[start.auxiliaryHead]?
      (if start.indexHead<n then some () else none) (start.work start.workHead)=
        .step q write .stay .stay .stay .stay (some e) :=
    origin_event_instruction P.bank (generatorData n) source negative start ready origin
      (.ready next) symbol e bankTable
  have mem := origin_event_memory P.bank (generatorData n) source negative start ready origin
    (.ready next) symbol e
  have tapes : Function.update source.tape j (Function.update (source.tape j) 0 symbol)=source.tape := by
    have blank : source.tape j 0=symbol := by
      change tape (before.store j) 0=(before.store j).head?
      rw [show before.store j=[] from empty]
      rfl
    rw [←blank,Function.update_eq_self,Function.update_eq_self]
  have memory : BankMemory P.bank (fun i=>tape (before.store i))
      (Function.update (fun i=>some (source.head i)) j none)
      (P.machine.stepConfiguration (generatorData n) start q write .stay .stay .stay .stay (some e)).work := by
    rw [selectedBank,tapes] at mem
    exact mem
  obtain ⟨ticks,target,sides,_,targetReady,path,_⟩ := bank_step_path P.bank (generatorData n) bits r
    source negative start ready bounded (.ready next) symbol .stay .stay .stay .stay (some e) bankTable
  have finalReady : BankReady P.bank (P.encoded (P.advance n before next .stay .stay (some e))) sides target := by
    simpa only [source,symbol,j,P.advance_stay] using targetReady
  refine ⟨q,write,action,memory,?_⟩
  cases ticks with
  | zero =>
      have same : start=target := by cases path; rfl
      have firstOutput := congrArg List.length ready.output
      have lastOutput := congrArg List.length finalReady.output
      rw [←same] at lastOutput
      simp only [encoded,advance,Option.toList_some,List.length_append,List.length_singleton] at firstOutput lastOutput
      omega
  | succ ticks =>
      obtain ⟨middle,edge,tail⟩ := path.first P.machine
      rw [P.machine.next_step _ _ _ _ _ _ _ _ _ _ action] at edge
      cases RunState.running.inj edge
      refine ⟨ticks,target,sides,finalReady,tail,?_⟩
      simp only [Machine.stepConfiguration]
      rw [finalReady.output]
      change before.output++[e]=start.output++[e]
      rw [ready.output]
      rfl

end
end ComplexityOfGenerators.Simulation.WordStack.Program
