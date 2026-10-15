import ComplexityOfGenerators.Simulation.TransducerBank.SpaceStep
import ComplexityOfGenerators.Simulation.TransducerBank.Random

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

/-- A random bank instruction uses one physical random read. The return scan
preserves that cursor, all input heads, all work tapes and accumulated output. -/
theorem bank_random_inRegion (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (negative : Fin k → Bool)
    (start : Configuration (bankMachine B)) (h : BankReady B source negative start)
    (bounded : B.Bounded data r source) (no yes : Q) (bit : Bool)
    (table : B.instruction data source = .readRandom no yes)
    (lookup : bits[source.randomHead]? = some bit)
    (region : (bankMachine B).InRegion r start) :
    ∃ ticks ready, ticks ≤ 2 * r + 4 ∧
      BankReady B (TapeBank.choose source (if bit then yes else no)) negative ready ∧
      (bankMachine B).Steps data bits start ticks ready ∧ (bankMachine B).InRegion r ready := by
  obtain ⟨ticks, ready, cost, related, path, visited⟩ :=
    bank_random_path B data bits r source negative start h bounded no yes bit table lookup
  exact ⟨ticks, ready, cost, related, path, visited r region (bounded.head _)⟩

/-- Observation of a terminal bank instruction, including actual random-tape
exhaustion, requires only the scan to the selected virtual head. -/
theorem bank_terminal_inRegion (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (negative : Fin k → Bool)
    (start : Configuration (bankMachine B)) (h : BankReady B source negative start)
    (bounded : B.Bounded data r source) (region : (bankMachine B).InRegion r start)
    (result : Outcome O)
    (terminal :
      (B.instruction data source = .accept ∧ result = .accepted source.output) ∨
      (B.instruction data source = .reject ∧ result = .rejected) ∨
      (∃ no yes, B.instruction data source = .readRandom no yes ∧
        bits[source.randomHead]? = none ∧ result = .exhausted)) :
    ∃ ready, (bankMachine B).Steps data bits start (source.head (B.select source.state)).natAbs ready ∧
      (bankMachine B).observe data bits ready = .halted result ∧
      (bankMachine B).InRegion r ready := by
  obtain ⟨ready, path, observed, visited⟩ :=
    bank_terminal_path B data bits r source negative start h bounded result terminal
  exact ⟨ready, path, observed, visited r region (bounded.head _)⟩


end
end ComplexityOfGenerators.Simulation.TransducerBank
