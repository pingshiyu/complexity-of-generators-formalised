import ComplexityOfGenerators.Simulation.TransducerBank.Execution

/-! A bank event selecting a head already at the common origin emits in one
real native step, before the ordinary two silent compiler bookkeeping steps. -/
namespace ComplexityOfGenerators.Simulation.TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A E Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype E]
    [Fintype Q] [Fintype S] (B : TapeBank I A E Q S k)

def eventWrite (start : Configuration (bankMachine B)) (j : Fin k) (write : S) :
    Option (Fin (Fintype.card (BankCell S k))) :=
  some (bankAlphabet {bankRead B (start.work 0) with
    symbol := Function.update (bankRead B (start.work 0)).symbol j write,
    marked := Function.update (bankRead B (start.work 0)).marked j false})

def eventNext (start : Configuration (bankMachine B)) (negative : Fin k→Bool) (j : Fin k) (next : Q) :
    Fin (Fintype.card (BankPhase Q k)) :=
  bankControl (.place next (Function.update negative j
    (bankSide (bankRead B (start.work 0)).origin (negative j) .stay)) j)

theorem origin_event_instruction (data : InputData I A) (source : BankConfiguration E Q S k)
    (negative : Fin k→Bool) (start : Configuration (bankMachine B))
    (ready : BankReady B source negative start) (atOrigin : source.head (B.select source.state)=0)
    (next : Q) (write : S) (event : E)
    (table : B.instruction data source=.step next write .stay .stay .stay .stay (some event)) :
    (bankMachine B).transition start.state data.input[start.inputHead]? data.auxiliary[start.auxiliaryHead]?
      (if start.indexHead<data.index then some () else none) (start.work start.workHead)=
      .step (eventNext B start negative (B.select source.state) next)
        (eventWrite B start (B.select source.state) write) .stay .stay .stay .stay (some event) := by
  rw [ready.state,ready.head]
  simp only [bankMachine,Equiv.symm_apply_apply,bankTransition]
  rw [ready.memory 0]
  simp only [bankCell,atOrigin,decide_true,Bool.not_true,Bool.false_eq_true,ite_false,
    ready.input,ready.auxiliary,ready.index]
  unfold TapeBank.instruction at table
  simp only [atOrigin,decide_true] at table
  rw [table]
  simp only [eventNext,eventWrite,ready.memory 0,bankCell,decide_true]

/-- The event step changes only the selected bank symbol/head marker; it does
not hide a scan or a change to another virtual tape. -/
theorem origin_event_memory (data : InputData I A) (source : BankConfiguration E Q S k)
    (negative : Fin k→Bool) (start : Configuration (bankMachine B))
    (ready : BankReady B source negative start) (atOrigin : source.head (B.select source.state)=0)
    (next : Q) (write : S) (event : E) :
    BankMemory B (Function.update source.tape (B.select source.state)
        (Function.update (source.tape (B.select source.state)) 0 write))
      (Function.update (fun j=>some (source.head j)) (B.select source.state) none)
      ((bankMachine B).stepConfiguration data start
        (eventNext B start negative (B.select source.state) next)
        (eventWrite B start (B.select source.state) write) .stay .stay .stay .stay (some event)).work := by
  change BankMemory B _ _ (Function.update start.work start.workHead
    (eventWrite B start (B.select source.state) write))
  rw [ready.head]
  exact ready.memory.write_clear B (B.select source.state) 0 write (by rw [atOrigin])

end
end ComplexityOfGenerators.Simulation.TransducerBank
