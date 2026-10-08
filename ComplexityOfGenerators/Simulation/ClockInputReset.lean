import ComplexityOfGenerators.Simulation.ClockTime

/-! A real tape scan resets the physical read-only input head after loading.
Its work head returns to the origin, and the clock/source tracks are unchanged. -/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} [Finite I] [Finite A]
variable (M : Machine I A O) (p : PolynomialBound)

def clockInputReset : Machine I A Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 3
  symbols := Fintype.card (ClockCell M.symbols p.degree) + 1
  initial := 0
  transition := fun state _ _ _ raw =>
    match state.val with
    | 0 => if (clockRead M p raw).last then .step 1 none .stay .stay .stay .stay none
      else .step 0 none .right .left .stay .stay none
    | 1 => if (clockRead M p raw).origin then .step 2 none .stay .stay .stay .stay none
      else .step 1 none .left .stay .stay .stay none
    | _ => .accept

theorem clock_input_reset (data : InputData I A) (bits : BitString) (length : ℕ)
    (start : Configuration (clockInputReset M p))
    (bounds : ReadHeadBounds (clockInputReset M p) data start)
    (inputBound : start.inputHead ≤ length)
    (state : start.state = (0 : Fin 3)) (head : start.workHead = 0)
    (last : ∀ i, (clockRead M p (start.work i)).last = decide (i = (length : ℤ)))
    (origin : ∀ i, (clockRead M p (start.work i)).origin = decide (i = 0)) :
    ∃ ready : Configuration (clockInputReset M p),
      ready.state = (1 : Fin 3) ∧ ready.workHead = 0 ∧ ready.inputHead = 0 ∧ ready.work = start.work ∧
      ready.randomHead = start.randomHead ∧ ready.output = start.output ∧
      ready.auxiliaryHead = start.auxiliaryHead ∧ ready.indexHead = start.indexHead ∧
      (clockInputReset M p).runFrom data bits start (2 * length + 1) = .running ready := by
  let N := clockInputReset M p
  obtain ⟨atEnd, endState, endHead, endMemory, endRandom, endOutput, endInput, endAux, endIndex, endRun⟩ :=
    tapeScan_inputLeft N data bits start (0 : Fin 3) (fun k => (k : ℤ)) (fun _ => .right) length bounds state head
      (fun k _ => by simp [Move.onInt])
      (fun k hk input auxiliary index => by
        have notEnd : (k : ℤ) ≠ (length : ℤ) := by omega
        simp [N, clockInputReset, last, notEnd])
  have atInput : atEnd.inputHead = 0 := by omega
  have endBounds : ReadHeadBounds N data atEnd := by
    constructor
    · rw [atInput]; omega
    · rw [endAux]; exact bounds.auxiliary
    · rw [endIndex]; exact bounds.index
  let entered := workStep N data atEnd (1 : Fin 3) none .stay
  have enterRun : N.runFrom data bits atEnd 1 = N.observe data bits entered := by
    apply workStep_run
    simp [N, clockInputReset, endState, endHead, endMemory, last]
  have enterFrame : WorkFrame N atEnd entered := workStep_frame N data atEnd (1 : Fin 3) none .stay endBounds
  obtain ⟨ready, scan, run⟩ := tapeScan_with_heads N data bits entered (1 : Fin 3)
    (fun k => ((length - k : ℕ) : ℤ)) (fun _ => .left) length
    (enterFrame.readHeadBounds N endBounds) rfl
    (by simpa [entered, workStep, Machine.stepConfiguration, Move.onInt] using endHead)
    (fun k hk => by simp only [Move.onInt]; omega)
    (fun k hk input auxiliary index => by
      have notOrigin : length - k ≠ 0 := by omega
      have tape : entered.work = start.work := endMemory
      simp [N, clockInputReset, tape, origin, notOrigin])
  have readyHead : ready.workHead = 0 := by simpa using scan.head
  have readyState : ready.state = (1 : Fin 3) := scan.state
  have readyMemory : ready.work = start.work := scan.memory.trans endMemory
  have live : N.observe data bits ready = .running ready := by
    simp [N, Machine.observe, clockInputReset, readyState, readyHead, readyMemory, origin]
  refine ⟨ready, readyState, readyHead, scan.input.trans (enterFrame.input.trans atInput), readyMemory,
    scan.random.trans endRandom, scan.output.trans endOutput, scan.auxiliary.trans (enterFrame.auxiliary.trans endAux),
    scan.index.trans (enterFrame.index.trans endIndex), ?_⟩
  have time : 2 * length + 1 = length + (1 + length) := by omega
  rw [time, N.runFrom_add data bits start atEnd length endRun,
    N.runFrom_add data bits atEnd entered 1 enterRun, run, live]

end

end ComplexityOfGenerators.Simulation
