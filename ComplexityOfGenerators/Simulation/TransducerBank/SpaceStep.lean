import ComplexityOfGenerators.Simulation.TransducerBank.Step
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceScans

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

/-- Simulation of one tape-bank instruction, including the return to origin.
The finite side bits implement two-way tapes, including crossing zero. -/
theorem bank_step_inRegion (data : InputData I A) (bits : BitString) (r : ℕ) (source : BankConfiguration O Q S k)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (h : BankReady B source negative start) (bounded : B.Bounded data r source)
    (next : Q) (write : S) (work input auxiliary index : Move) (emit : Option O)
    (table : B.instruction data source = .step next write work input auxiliary index emit)
    (region : (bankMachine B).InRegion r start)
    (successorBound : B.Bounded data r (B.advance data source next write work input auxiliary index emit)) :
    ∃ t ready sides, t ≤ 2 * r + 4 ∧
      BankReady B (B.advance data source next write work input auxiliary index emit) sides ready ∧
      (bankMachine B).Steps data bits start t ready ∧ (bankMachine B).InRegion r ready := by
  obtain ⟨t, ready, sides, cost, related, path, visited⟩ :=
    bank_step_path B data bits r source negative start h bounded next write work input auxiliary index emit table
  refine ⟨t, ready, sides, cost, related, path, visited r region (bounded.head _) ?_⟩
  simpa [TapeBank.advance] using successorBound.head (B.select source.state)

end
end ComplexityOfGenerators.Simulation.TransducerBank
