import ComplexityOfGenerators.Simulation.TransducerBank.Compiler

namespace ComplexityOfGenerators.Simulation.TransducerBank

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} [Fintype I] [Fintype A] [Fintype O]
  [Fintype Q] [Fintype S] (B : TapeBank I A O Q S k)

theorem bank_seek (data : InputData I A) (bits : BitString) (r : ℕ) (source : BankConfiguration O Q S k)
    (negative : Fin k → Bool) (start : Configuration (bankMachine B))
    (h : BankReady B source negative start) (bounded : B.Bounded data r source) :
    ∃ ready, ScanResult (bankMachine B) start ready (source.head (B.select source.state)) ∧
      (bankMachine B).runFrom data bits start
        (source.head (B.select source.state)).natAbs =
          (bankMachine B).observe data bits ready := by
  let j := B.select source.state
  let distance := (source.head j).natAbs
  have position := signedPosition_natAbs (source.head j) (negative j) (h.side j)
  have memory := h.memory
  unfold BankMemory at memory
  obtain ⟨ready, scan, run⟩ := tapeScan_with_heads (bankMachine B) data bits start
    (bankControl (.seek source.state negative)) (signedPosition (negative j))
    (fun _ => if negative j then .left else .right) distance
    (h.toBankSnapshot.readHeadBounds B bounded) h.state (by simpa using h.head)
    (fun n _ => signedPosition_out (negative j) n)
    (fun n hn input auxiliary index => by
      have different : source.head j ≠ signedPosition (negative j) n := by
        rw [position]
        cases side : negative j <;> simp only [signedPosition, side, Bool.false_eq_true,
          ↓reduceIte] <;> dsimp [distance] at hn <;> omega
      dsimp [j] at different
      simp [bankMachine, bankTransition, memory, bankCell, j, different])
  refine ⟨ready, ?_, run⟩
  simpa only [distance, ← position] using scan

theorem bank_back (data : InputData I A) (bits : BitString) (start : Configuration (bankMachine B))
    (q : Q) (negative : Fin k → Bool) (side : Bool) (distance : ℕ)
    (bounds : ReadHeadBounds (bankMachine B) data start)
    (state : start.state = bankControl (.back q negative side))
    (head : start.workHead = signedPosition side distance)
    (origin : ∀ i, (bankRead B (start.work i)).origin = decide (i = 0)) :
    ∃ ready, ScanResult (bankMachine B) start ready 0 ∧
      (bankMachine B).runFrom data bits start distance =
        (bankMachine B).observe data bits ready := by
  obtain ⟨ready, scan, run⟩ := tapeScan_with_heads (bankMachine B) data bits start
    (bankControl (.back q negative side)) (fun n => signedPosition side (distance - n))
    (fun _ => if side then .right else .left) distance bounds state (by simpa using head)
    (fun n hn => by rw [signedPosition_in side _ (by omega)]; congr 1)
    (fun n hn input auxiliary index => by
      have nonzero := signedPosition_ne_zero side (show 0 < distance - n by omega)
      simp [bankMachine, bankTransition, origin, nonzero])
  exact ⟨ready, by simpa using scan, run⟩

theorem bankSide_correct (position : ℤ) (negative : Bool) (move : Move)
    (h : if negative then position ≤ 0 else 0 ≤ position) :
    if bankSide (decide (position = 0)) negative move then
      move.onInt position ≤ 0 else 0 ≤ move.onInt position := by
  cases negative <;> cases move <;> simp_all [bankSide, Move.onInt] <;> omega

/-- The initial origin and all head markers are written by one real native
instruction; the simulation never assumes a preinitialized work tape. -/
theorem bank_loaded (data : InputData I A) (bits : BitString) :
    ∃ ready, BankReady B B.initialConfiguration (fun _ => false) ready ∧
      (bankMachine B).run data bits 1 =
        (bankMachine B).observe data bits ready := by
  let M := bankMachine B
  let ready := M.stepConfiguration data M.initialConfiguration
    (bankControl (.seek B.initial (fun _ => false)))
    (some (bankAlphabet ⟨fun _ => B.blank, fun _ => true, true⟩)) .stay .stay .stay .stay none
  refine ⟨ready, ?_, ?_⟩
  · constructor
    · constructor
      · intro i
        change bankRead B (Function.update (fun _ => none) 0
          (some (bankAlphabet ⟨fun _ => B.blank, fun _ => true, true⟩)) i) = _
        by_cases zero : i = 0
        · subst i
          simp [bankCell, TapeBank.initialConfiguration]
        · simp [Function.update_of_ne zero, bankRead, bankBlank, bankCell,
            TapeBank.initialConfiguration, zero, Ne.symm zero]
      · rfl
      · rfl
      · rfl
      · rfl
      · rfl
    · rfl
    · rfl
    · simp [TapeBank.initialConfiguration]
  · rw [← M.runFrom_initial]
    have table : M.transition M.initialConfiguration.state data.input[0]? data.auxiliary[0]?
        (if 0 < data.index then some () else none) none =
        .step (bankControl (.seek B.initial (fun _ => false)))
          (some (bankAlphabet ⟨fun _ => B.blank, fun _ => true, true⟩)) .stay .stay .stay .stay none := by
      simp [M, bankMachine, Machine.initialConfiguration, bankTransition]
    exact M.runFrom_shift data bits M.initialConfiguration ready
      (M.observe_step _ _ _ _ _ _ _ _ _ _ (by simpa [Machine.initialConfiguration] using table))
      (M.next_step _ _ _ _ _ _ _ _ _ _ (by simpa [Machine.initialConfiguration] using table)) 0

end
end ComplexityOfGenerators.Simulation.TransducerBank
