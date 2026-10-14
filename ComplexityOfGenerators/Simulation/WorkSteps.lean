import ComplexityOfGenerators.Simulation.TapeScan
import ComplexityOfGenerators.Foundations.ExecutionBounds

/-! Composable specifications for work-only primitive instructions. They
account for actual native transitions and preserve all suspended input heads. -/

namespace ComplexityOfGenerators.Simulation

variable {I A O : Type} (M : Machine I A O)

theorem ReadHeadBounds.stepConfiguration (data : InputData I A) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols))
    (work input auxiliary index : Move) (emit : Option O) (bounds : ReadHeadBounds M data c) :
    ReadHeadBounds M data (M.stepConfiguration data c state write work input auxiliary index emit) :=
  ⟨input.onInput_le _ _ bounds.input, auxiliary.onInput_le _ _ bounds.auxiliary,
    index.onInput_le _ _ bounds.index⟩

structure WorkFrame (start ready : Configuration M) : Prop where
  random : ready.randomHead = start.randomHead
  output : ready.output = start.output
  input : ready.inputHead = start.inputHead
  auxiliary : ready.auxiliaryHead = start.auxiliaryHead
  index : ready.indexHead = start.indexHead

theorem WorkFrame.refl (c : Configuration M) : WorkFrame M c c := ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem WorkFrame.trans {a b c : Configuration M} (hab : WorkFrame M a b)
    (hbc : WorkFrame M b c) : WorkFrame M a c :=
  ⟨hbc.random.trans hab.random, hbc.output.trans hab.output, hbc.input.trans hab.input,
    hbc.auxiliary.trans hab.auxiliary, hbc.index.trans hab.index⟩

theorem WorkFrame.readHeadBounds {data : InputData I A} {a b : Configuration M}
    (frame : WorkFrame M a b) (bounds : ReadHeadBounds M data a) : ReadHeadBounds M data b := by
  constructor
  · rw [frame.input]; exact bounds.input
  · rw [frame.auxiliary]; exact bounds.auxiliary
  · rw [frame.index]; exact bounds.index

theorem ScanResult.workFrame {a b : Configuration M} {head : ℤ}
    (scan : ScanResult M a b head) : WorkFrame M a b :=
  ⟨scan.random, scan.output, scan.input, scan.auxiliary, scan.index⟩

def workStep (data : InputData I A) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols)) (move : Move) : Configuration M :=
  M.stepConfiguration data c state write move .stay .stay .stay none

theorem workStep_frame (data : InputData I A) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols)) (move : Move)
    (bounds : ReadHeadBounds M data c) : WorkFrame M c (workStep M data c state write move) := by
  refine ⟨rfl, rfl, ?_, ?_, ?_⟩
  · exact Nat.min_eq_left bounds.input
  · exact Nat.min_eq_left bounds.auxiliary
  · exact Nat.min_eq_left bounds.index

theorem workStep_run (data : InputData I A) (bits : BitString) (c : Configuration M)
    (state : Fin M.states) (write : Option (Fin M.symbols)) (move : Move)
    (table : M.transition c.state data.input[c.inputHead]? data.auxiliary[c.auxiliaryHead]?
      (if c.indexHead < data.index then some () else none) (c.work c.workHead) =
        .step state write move .stay .stay .stay none) :
    M.runFrom data bits c 1 = M.observe data bits (workStep M data c state write move) :=
  M.runFrom_shift data bits c _ (M.observe_step data bits c _ _ _ _ _ _ _ table)
    (M.next_step data bits c _ _ _ _ _ _ _ table) 0

end ComplexityOfGenerators.Simulation
