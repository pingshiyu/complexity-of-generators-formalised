import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixInsertCodec
import ComplexityOfGenerators.Simulation.WordStack.InsertAt

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert

open Simulation.WordStack

structure State where
  word : List Symbol
  incoming : List Symbol
  outRev : List Symbol
  deriving DecidableEq

def step (size position : ℕ) (state : State) : State :=
  ⟨state.word.drop size, state.incoming.tail,
    (InsertAt.insertAt (state.word.take size) position
      (state.incoming.headD (.bit false))).reverse ++ state.outRev⟩

def columns (position : ℕ) : List (List Symbol) → List Symbol → List (List Symbol)
  | [], _ => []
  | row :: rest, incoming =>
      InsertAt.insertAt row position (incoming.headD (.bit false)) ::
        columns position rest incoming.tail

def value (size position : ℕ) (newRow : List Symbol) (state : State) : State :=
  let first := (step size position)^[position] state
  (step size position)^[size-position] { first with outRev := newRow.reverse ++ first.outRev }

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.MatrixInsert
