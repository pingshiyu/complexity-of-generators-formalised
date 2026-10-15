import ComplexityOfGenerators.Simulation.TransducerBank.Step

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

/-- A random bank instruction uses one physical random read. The return scan
preserves that cursor, all input heads, all work tapes and accumulated output. -/
theorem bank_random_path (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (negative : Fin k → Bool)
    (start : Configuration (bankMachine B)) (h : BankReady B source negative start)
    (bounded : B.Bounded data r source) (no yes : Q) (bit : Bool)
    (table : B.instruction data source = .readRandom no yes)
    (lookup : bits[source.randomHead]? = some bit) :
    ∃ ticks ready, ticks ≤ 2 * r + 4 ∧
      BankReady B (TapeBank.choose source (if bit then yes else no)) negative ready ∧
      (bankMachine B).Steps data bits start ticks ready ∧
      ∀ s, (bankMachine B).InRegion s start → (source.head (B.select source.state)).natAbs ≤ s →
        (bankMachine B).InRegion s ready := by
  let M := bankMachine B
  let j := B.select source.state
  let position := source.head j
  let q := if bit then yes else no
  let advanced := TapeBank.choose source q
  obtain ⟨fetched, scan, fetchPath, fetchedRegion⟩ :=
    bank_seek_path B data bits r source negative start h bounded
  have snap := h.toBankSnapshot.scan B scan
  have memory := snap.memory
  unfold BankMemory at memory
  have action : M.transition fetched.state data.input[fetched.inputHead]? data.auxiliary[fetched.auxiliaryHead]?
      (if fetched.indexHead < data.index then some () else none) (fetched.work fetched.workHead) =
      .readRandom (bankControl (.back no negative (negative j)))
        (bankControl (.back yes negative (negative j))) := by
    rw [scan.state, h.state]
    simp only [M, bankMachine, Equiv.symm_apply_apply, bankTransition]
    rw [scan.head, memory]
    simp only [bankCell, Option.some.injEq, decide_true, Bool.not_true, Bool.false_eq_true,
      ↓reduceIte, snap.input, snap.auxiliary, snap.index]
    unfold TapeBank.instruction at table
    rw [table]
  let chosen : Configuration M :=
    {fetched with state := bankControl (.back q negative (negative j)), randomHead := source.randomHead + 1}
  have next : M.next data bits fetched = .running chosen := by
    cases bit <;> simp [Machine.next, action, snap.random, lookup, chosen, q]
  have chosenSnap : BankSnapshot B advanced chosen :=
    ⟨snap.memory, snap.input, snap.auxiliary, snap.index, rfl, snap.output⟩
  have advancedBound : B.Bounded data r advanced :=
    ⟨bounded.input, bounded.auxiliary, bounded.index, bounded.head⟩
  have chosenHead : chosen.workHead = signedPosition (negative j) position.natAbs :=
    scan.head.trans (signedPosition_natAbs position (negative j) (h.side j))
  obtain ⟨returned, backScan, backPath, returnedRegion⟩ :=
    bank_back_path B data bits chosen q negative (negative j) position.natAbs
    (chosenSnap.readHeadBounds B advancedBound) rfl chosenHead (fun i => by rw [chosenSnap.memory]; rfl)
  have returnedSnap := chosenSnap.scan B backScan
  have returnedMemory := returnedSnap.memory
  unfold BankMemory at returnedMemory
  let ready := workStep M data returned (bankControl (.seek q negative)) none .stay
  have finishPath : M.Steps data bits returned 1 ready := by
    apply workStep_path
    rw [backScan.state]
    simp [M, chosen, bankMachine, bankTransition, backScan.head, returnedMemory, bankCell]
  have frame := workStep_frame M data returned (bankControl (.seek q negative)) none .stay
    (returnedSnap.readHeadBounds B advancedBound)
  refine ⟨position.natAbs + (1 + (position.natAbs + 1)), ready, ?_, ?_, ?_, ?_⟩
  · have := bounded.head j
    dsimp [position] at *
    omega
  · constructor
    · exact ⟨returnedSnap.memory, frame.input.trans returnedSnap.input,
        frame.auxiliary.trans returnedSnap.auxiliary, frame.index.trans returnedSnap.index,
        frame.random.trans returnedSnap.random, frame.output.trans returnedSnap.output⟩
    · rfl
    · exact backScan.head
    · exact h.side
  · exact fetchPath.trans M ((Machine.Steps.tail .refl next).trans M (backPath.trans M finishPath))
  · intro s region radius
    apply (returnedRegion s (fetchedRegion s region radius) radius).step M
    change -(s : ℤ) ≤ returned.workHead ∧ returned.workHead ≤ s
    rw [backScan.head]
    constructor <;> omega

/-- Observation of a terminal bank instruction, including actual random-tape
exhaustion, requires only the scan to the selected virtual head. -/
theorem bank_terminal_path (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (negative : Fin k → Bool)
    (start : Configuration (bankMachine B)) (h : BankReady B source negative start)
    (bounded : B.Bounded data r source)
    (result : Outcome O)
    (terminal :
      (B.instruction data source = .accept ∧ result = .accepted source.output) ∨
      (B.instruction data source = .reject ∧ result = .rejected) ∨
      (∃ no yes, B.instruction data source = .readRandom no yes ∧
        bits[source.randomHead]? = none ∧ result = .exhausted)) :
    ∃ ready, (bankMachine B).Steps data bits start (source.head (B.select source.state)).natAbs ready ∧
      (bankMachine B).observe data bits ready = .halted result ∧
      (∀ s, (bankMachine B).InRegion s start → (source.head (B.select source.state)).natAbs ≤ s →
        (bankMachine B).InRegion s ready) := by
  obtain ⟨ready, scan, path, visited⟩ :=
    bank_seek_path B data bits r source negative start h bounded
  refine ⟨ready, path, ?_, visited⟩
  have snap := h.toBankSnapshot.scan B scan
  have memory := snap.memory
  unfold BankMemory at memory
  rcases terminal with ⟨table, rfl⟩ | ⟨table, rfl⟩ | ⟨no, yes, table, absent, rfl⟩
  · unfold TapeBank.instruction at table
    simp [Machine.observe, bankMachine, bankTransition, scan.state, h.state,
      scan.head, memory, bankCell, snap.input, snap.auxiliary, snap.index, table, snap.output]
  · unfold TapeBank.instruction at table
    simp [Machine.observe, bankMachine, bankTransition, scan.state, h.state,
      scan.head, memory, bankCell, snap.input, snap.auxiliary, snap.index, table]
  · have unavailable : ¬source.randomHead < bits.length := by
      have := List.getElem?_eq_none_iff.mp absent
      omega
    unfold TapeBank.instruction at table
    simp [Machine.observe, bankMachine, bankTransition, scan.state, h.state,
      scan.head, memory, bankCell, snap.input, snap.auxiliary, snap.index, table, snap.random, unavailable]

/-- A random bank instruction uses one physical random read. The return scan
preserves that cursor, all input heads, all work tapes and accumulated output. -/
theorem bank_random (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (negative : Fin k → Bool)
    (start : Configuration (bankMachine B)) (h : BankReady B source negative start)
    (bounded : B.Bounded data r source) (no yes : Q) (bit : Bool)
    (table : B.instruction data source = .readRandom no yes)
    (lookup : bits[source.randomHead]? = some bit) :
    ∃ ticks ready, ticks ≤ 2 * r + 4 ∧
      BankReady B (TapeBank.choose source (if bit then yes else no)) negative ready ∧
      (bankMachine B).runFrom data bits start ticks = (bankMachine B).observe data bits ready := by
  obtain ⟨ticks, ready, cost, related, path, _⟩ :=
    bank_random_path B data bits r source negative start h bounded no yes bit table lookup
  exact ⟨ticks, ready, cost, related, path.runFrom (bankMachine B)⟩

/-- Observation of a terminal bank instruction, including actual random-tape
exhaustion, requires only the scan to the selected virtual head. -/
theorem bank_terminal (data : InputData I A) (bits : BitString) (r : ℕ)
    (source : BankConfiguration O Q S k) (negative : Fin k → Bool)
    (start : Configuration (bankMachine B)) (h : BankReady B source negative start)
    (bounded : B.Bounded data r source) (result : Outcome O)
    (terminal :
      (B.instruction data source = .accept ∧ result = .accepted source.output) ∨
      (B.instruction data source = .reject ∧ result = .rejected) ∨
      (∃ no yes, B.instruction data source = .readRandom no yes ∧
        bits[source.randomHead]? = none ∧ result = .exhausted)) :
    (bankMachine B).runFrom data bits start (source.head (B.select source.state)).natAbs = .halted result := by
  obtain ⟨ready, path, observed, _⟩ :=
    bank_terminal_path B data bits r source negative start h bounded result terminal
  exact (path.runFrom (bankMachine B)).trans observed

end
end ComplexityOfGenerators.Simulation.TransducerBank
