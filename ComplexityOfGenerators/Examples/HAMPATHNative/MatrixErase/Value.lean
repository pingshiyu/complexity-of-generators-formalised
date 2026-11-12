import ComplexityOfGenerators.Examples.HAMPATHParser

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase

structure State where
  word : List Symbol
  countdown : ℕ
  pending : Bool
  outRev : List Symbol

def step (size start : ℕ) (state : State) : State :=
  ⟨state.word.drop size, state.countdown - 1,
    if state.countdown = 0 then false else state.pending,
    if state.countdown = 0 ∧ state.pending = true then state.outRev
    else ((state.word.take size).eraseIdx start).reverse ++ state.outRev⟩

end ComplexityOfGenerators.Examples.HAMPATH.Native.MatrixErase
