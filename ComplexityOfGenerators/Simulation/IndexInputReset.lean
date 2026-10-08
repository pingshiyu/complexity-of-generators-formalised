import ComplexityOfGenerators.Simulation.VirtualIndexPolynomial
import ComplexityOfGenerators.Simulation.WorkSteps

/-! Preparing the exact virtual index equal to the ordinary input length.
The block loader supplies one extra live origin cell. A native scan resets the
ordinary input head and clears that last live cell, including at size zero. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

omit [Fintype α] in
theorem VirtualIndexMemory.erase_last (n : ℕ) (work : ℤ → Option (Fin M.symbols))
    (ih wh : Option ℤ) (memory : ℤ → Option (Fin (Fintype.card (IndexCell M.symbols) + 1)))
    (h : VirtualIndexMemory M (n + 1) work ih wh memory) :
    VirtualIndexMemory M n work ih wh
      (Function.update memory (n : ℤ) (some (indexWrite M {indexRead M (memory n) with live := false}))) := by
  intro i
  by_cases same : i = (n : ℤ)
  · subst i
    rw [Function.update_self, indexRead_write, h]
    simp [virtualIndexCell]
  · rw [Function.update_of_ne same, h]
    have live : (0 ≤ i ∧ i < ((n + 1 : ℕ) : ℤ)) ↔ (0 ≤ i ∧ i < (n : ℤ)) := by omega
    simp only [virtualIndexCell, live]

def indexInputReset : Machine α Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 4
  symbols := Fintype.card (IndexCell M.symbols) + 1
  initial := 0
  transition := fun state _ _ _ raw =>
    let cell := indexRead M raw
    match state.val with
    | 0 => if cell.live then .step 0 none .right .left .stay .stay none
      else .step 1 none .left .stay .stay .stay none
    | 1 => .step 2 (some (indexWrite M {cell with live := false})) .stay .stay .stay .stay none
    | 2 => if cell.origin then .step 3 none .stay .stay .stay .stay none
      else .step 2 none .left .stay .stay .stay none
    | _ => .accept

theorem index_input_reset (data : InputData α Bool) (bits : BitString) (n : ℕ)
    (work : ℤ → Option (Fin M.symbols)) (ih wh : Option ℤ)
    (start : Configuration (indexInputReset M))
    (bounds : ReadHeadBounds (indexInputReset M) data start)
    (inputBound : start.inputHead ≤ n)
    (state : start.state = (0 : Fin 4)) (head : start.workHead = 0)
    (memory : VirtualIndexMemory M (n + 1) work ih wh start.work) :
    ∃ ready : Configuration (indexInputReset M),
      ready.state = (2 : Fin 4) ∧ ready.workHead = 0 ∧ ready.inputHead = 0 ∧
      VirtualIndexMemory M n work ih wh ready.work ∧
      ready.randomHead = start.randomHead ∧ ready.output = start.output ∧
      ready.auxiliaryHead = start.auxiliaryHead ∧ ready.indexHead = start.indexHead ∧
      (indexInputReset M).runFrom data bits start (2 * n + 3) = .running ready := by
  let N := indexInputReset M
  obtain ⟨atEnd, endState, endHead, endMemory, endRandom, endOutput, endInput, endAux, endIndex, endRun⟩ :=
    tapeScan_inputLeft N data bits start (0 : Fin 4) (fun k => (k : ℤ)) (fun _ => .right) (n + 1) bounds state head
      (fun k _ => by simp [Move.onInt])
      (fun k hk input auxiliary index => by
        simp [N, indexInputReset, memory _, virtualIndexCell]
        omega)
  have atInput : atEnd.inputHead = 0 := by omega
  have endBounds : ReadHeadBounds N data atEnd := by
    constructor
    · rw [atInput]; omega
    · rw [endAux]; exact bounds.auxiliary
    · rw [endIndex]; exact bounds.index
  let lastCell := workStep N data atEnd (1 : Fin 4) none .left
  have lastRun : N.runFrom data bits atEnd 1 = N.observe data bits lastCell := by
    apply workStep_run
    simp [N, indexInputReset, endState, endHead, endMemory, memory _, virtualIndexCell]
  have lastFrame : WorkFrame N atEnd lastCell := workStep_frame N data atEnd _ none .left endBounds
  have lastHead : lastCell.workHead = (n : ℤ) := by
    simp [lastCell, workStep, Machine.stepConfiguration, Move.onInt, endHead]
  have lastMemory : VirtualIndexMemory M (n + 1) work ih wh lastCell.work := by
    change VirtualIndexMemory M (n + 1) work ih wh atEnd.work
    rw [endMemory]; exact memory
  let cleared := workStep N data lastCell (2 : Fin 4)
    (some (indexWrite M {indexRead M (lastCell.work lastCell.workHead) with live := false})) .stay
  have clearRun : N.runFrom data bits lastCell 1 = N.observe data bits cleared := by
    apply workStep_run
    simp [N, indexInputReset, lastCell, workStep, Machine.stepConfiguration]
  have clearFrame : WorkFrame N lastCell cleared := workStep_frame N data lastCell _ _ .stay
    (lastFrame.readHeadBounds N endBounds)
  have clearedMemory : VirtualIndexMemory M n work ih wh cleared.work := by
    simpa only [cleared, workStep, Machine.stepConfiguration, lastHead] using
      lastMemory.erase_last M n work ih wh lastCell.work
  obtain ⟨ready, scan, run⟩ := tapeScan_with_heads N data bits cleared (2 : Fin 4)
    (fun k => ((n - k : ℕ) : ℤ)) (fun _ => .left) n
    (clearFrame.readHeadBounds N (lastFrame.readHeadBounds N endBounds)) rfl
    (by simpa [cleared, workStep, Machine.stepConfiguration, Move.onInt] using lastHead)
    (fun k hk => by simp only [Move.onInt]; omega)
    (fun k hk input auxiliary index => by
      have nonzero : n - k ≠ 0 := by omega
      simp [N, indexInputReset, clearedMemory _, virtualIndexCell, nonzero])
  have readyHead : ready.workHead = 0 := by simpa using scan.head
  have readyState : ready.state = (2 : Fin 4) := scan.state
  have readyMemory : VirtualIndexMemory M n work ih wh ready.work := by rw [scan.memory]; exact clearedMemory
  have live : N.observe data bits ready = .running ready := by
    simp [N, Machine.observe, indexInputReset, readyState, readyHead, readyMemory _, virtualIndexCell]
  have frame := lastFrame.trans N (clearFrame.trans N (scan.workFrame N))
  refine ⟨ready, readyState, readyHead, frame.input.trans atInput, readyMemory,
    frame.random.trans endRandom, frame.output.trans endOutput, frame.auxiliary.trans endAux, frame.index.trans endIndex, ?_⟩
  have time : 2 * n + 3 = (n + 1) + (1 + (1 + n)) := by omega
  rw [time, N.runFrom_add data bits start atEnd (n + 1) endRun,
    N.runFrom_add data bits atEnd lastCell 1 lastRun, N.runFrom_add data bits lastCell cleared 1 clearRun, run, live]

end

end ComplexityOfGenerators.Simulation
