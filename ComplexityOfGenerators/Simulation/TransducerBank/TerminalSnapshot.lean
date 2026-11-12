import ComplexityOfGenerators.Simulation.TransducerBank.Execution

namespace ComplexityOfGenerators.Simulation.TransducerBank
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {I A E Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype E]
    [Fintype Q] [Fintype S] (B : TapeBank I A E Q S k)

theorem bank_accepting_path (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration E Q S k) (negative : Fin k→Bool)
    (start : Configuration (bankMachine B)) (ready : BankReady B source negative start)
    (bounded : B.Bounded data r source) (table : B.instruction data source=.accept) :
    ∃ last, (bankMachine B).Steps data bits start (source.head (B.select source.state)).natAbs last ∧
      BankSnapshot B source last ∧
      (bankMachine B).observe data bits last=.halted (.accepted source.output) := by
  obtain ⟨last,scan,path,_⟩ := bank_seek_path B data bits r source negative start ready bounded
  have snapshot := ready.toBankSnapshot.scan B scan
  refine ⟨last,path,snapshot,?_⟩
  have memory := snapshot.memory
  unfold BankMemory at memory
  unfold TapeBank.instruction at table
  simp [Machine.observe,bankMachine,bankTransition,scan.state,ready.state,
    scan.head,memory,bankCell,snapshot.input,snapshot.auxiliary,snapshot.index,table,snapshot.output]

theorem bank_exhausted_path (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration E Q S k) (negative : Fin k→Bool)
    (start : Configuration (bankMachine B)) (ready : BankReady B source negative start)
    (bounded : B.Bounded data r source) (no yes : Q)
    (table : B.instruction data source=.readRandom no yes) (absent : bits[source.randomHead]?=none) :
    ∃ last, (bankMachine B).Steps data bits start (source.head (B.select source.state)).natAbs last ∧
      BankSnapshot B source last ∧ (bankMachine B).observe data bits last=.halted .exhausted := by
  obtain ⟨last,scan,path,_⟩ := bank_seek_path B data bits r source negative start ready bounded
  have snapshot := ready.toBankSnapshot.scan B scan
  have memory := snapshot.memory
  unfold BankMemory at memory
  have unavailable : ¬source.randomHead<bits.length := by
    have bound := List.getElem?_eq_none_iff.mp absent
    omega
  refine ⟨last,path,snapshot,?_⟩
  unfold TapeBank.instruction at table
  simp [Machine.observe,bankMachine,bankTransition,scan.state,ready.state,scan.head,memory,bankCell,
    snapshot.input,snapshot.auxiliary,snapshot.index,table,snapshot.random,unavailable]

end
end ComplexityOfGenerators.Simulation.TransducerBank
