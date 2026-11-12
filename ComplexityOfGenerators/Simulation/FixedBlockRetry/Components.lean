import ComplexityOfGenerators.Simulation.FixedBlockRetry.Collect
import ComplexityOfGenerators.Simulation.WordStack.Unary
import ComplexityOfGenerators.Simulation.WordStack.Output
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Simulation.FixedBlockRetry

open WordStack

variable {S O : Type} [Fintype S]

def flagWord (unitSymbol : S) (value : Bool) : List S := if value then [unitSymbol] else []

/-- A semantic fact about an actual finite routine on a complete collected
block. It imposes no abstract implementation or simulation assumption. -/
def PhaseCorrect {Payload : Type} (unitSymbol : S) (bitSymbol : Bool → S) (decode : S → Option Payload)
    (width : PolynomialBound) (phase : WordStack.Routine S O 35)
    (f : ℕ → BitString → Option (List Payload)) : Prop :=
  ∀ (n : ℕ) (block : BitString) (s : Local.Store S 35), block.length = width n → (s 13).length = n → (s 22).length = n →
    s 17 = block.map bitSymbol →
      (phase.eval s 32 = flagWord unitSymbol (f n block).isSome ∧
        ∀ word, f n block = some word → (phase.eval s 31).filterMap decode = word)

/-- Uniform bounds on the stores and primitive instructions of that routine. -/
def PhaseBound (bitSymbol : Bool → S) (width cap time : PolynomialBound)
    (phase : WordStack.Routine S O 35) : Prop :=
  ∀ (n : ℕ) (block : BitString) (s : Local.Store S 35), block.length = width n → (s 13).length = n → (s 22).length = n →
    s 17 = block.map bitSymbol → StoreBound s (cap n) →
      StoreBound (phase.eval s) (cap n) ∧ phase.cost s ≤ time n

def restoreIndex (unitSymbol : S) : WordStack.Routine S O 35 :=
  WordStack.Routine.assign 22 13 33 (by decide) (by decide) (by decide) (fun _ => unitSymbol)

def setup (unitSymbol : S) : WordStack.Routine S O 35 :=
  (WordStack.Routine.assign 13 22 33 (by decide) (by decide) (by decide) id).seq
  ((WordStack.Routine.clear 31).seq (WordStack.Routine.clear 32))

def attempt (unitSymbol : S) (bitSymbol : Bool → S) (width : PolynomialBound)
    (phase : WordStack.Routine S O 35) : Command S O 35 :=
  (collectCommand unitSymbol bitSymbol width).seq
    (phase.command.seq (restoreIndex unitSymbol).command)

def retryLoop (unitSymbol : S) (bitSymbol : Bool → S) (width : PolynomialBound)
    (phase : WordStack.Routine S O 35) : Command S O 35 :=
  .loop 32 (fun observed => observed.1.isNone) (attempt unitSymbol bitSymbol width phase)

def command (unitSymbol : S) (bitSymbol : Bool → S) (decode : S → Option O)
    (width : PolynomialBound) (phase : WordStack.Routine S O 35) : Command S O 35 :=
  (Command.loadIndex 13 unitSymbol).seq
  ((setup unitSymbol).command.seq
  ((retryLoop unitSymbol bitSymbol width phase).seq (Command.emitWord 31 decode)))

/-- The payload selected by the loop, before its final output instructions. -/
def selected {Payload : Type} (decode : S → Option Payload) : Result S O 35 → Option (List Payload)
  | .exhausted => none
  | .done memory => some ((memory.store 31).filterMap decode)

end ComplexityOfGenerators.Simulation.FixedBlockRetry
