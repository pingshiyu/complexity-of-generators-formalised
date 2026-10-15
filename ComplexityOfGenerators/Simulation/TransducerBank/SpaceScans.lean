import ComplexityOfGenerators.Simulation.TransducerBank.Scans
import ComplexityOfGenerators.Simulation.TapeScanSpace

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

theorem bank_seek_inRegion (data : InputData I A) (bits : BitString) (r : ℕ) (source : BankConfiguration O Q S k)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (h : BankReady B source negative start) (bounded : B.Bounded data r source)
    (region : (bankMachine B).InRegion r start) :
    ∃ ready, ScanResult (bankMachine B) start ready (source.head (B.select source.state)) ∧
      (bankMachine B).Steps data bits start (source.head (B.select source.state)).natAbs ready ∧
      (bankMachine B).InRegion r ready := by
  obtain ⟨ready, scan, path, visited⟩ := bank_seek_path B data bits r source negative start h bounded
  exact ⟨ready, scan, path, visited r region (bounded.head _)⟩

theorem bank_back_inRegion (data : InputData I A) (bits : BitString) (start : Configuration (bankMachine B))
    (q : Q) (negative : Fin k → Bool) (side : Bool) (distance r : ℕ)
    (radius : distance ≤ r) (region : (bankMachine B).InRegion r start)
    (bounds : ReadHeadBounds (bankMachine B) data start)
    (state : start.state = bankControl (.back q negative side))
    (head : start.workHead = signedPosition side distance)
    (origin : ∀ i, (bankRead B (start.work i)).origin = decide (i = 0)) :
    ∃ ready, ScanResult (bankMachine B) start ready 0 ∧
      (bankMachine B).Steps data bits start distance ready ∧
      (bankMachine B).InRegion r ready := by
  obtain ⟨ready, scan, path, visited⟩ := bank_back_path B data bits start q negative side distance bounds state head origin
  exact ⟨ready, scan, path, visited r region radius⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank
