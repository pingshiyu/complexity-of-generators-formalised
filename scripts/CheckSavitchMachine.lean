import ComplexityOfGenerators.Simulation.SavitchMachine.ConstantBase
import ComplexityOfGenerators.Simulation.SavitchMachine.Ruler

/-! End-to-end executable checks of the concrete recursive machine. These
exercise the actual field-copy, counter, return, and dispatch instructions;
the general simulation proofs are in `SavitchMachine.Execution` and `AlphabetSearch`.
Run with `lake env lean scripts/CheckSavitchMachine.lean` after `lake build`. -/

open ComplexityOfGenerators Simulation StackSpace SavitchMachine Complexity

namespace SavitchMachineChecks

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def root (depth width : ℕ) : Sav.Sst :=
  ⟨false, false, none,
    [⟨true, false, List.replicate depth false, List.replicate width false,
      List.replicate width false, List.replicate width false⟩]⟩

def run (result : Bool) (input : List Bool) :
    ℕ → Source (Alphabet Bool) (Label Unit) (Status × Option (Alphabet Bool)) 12 → Option (Bool × Bool)
  | 0, _ => none
  | fuel + 1, c =>
      match Turing.TM2.step (AlphabetSearch.program () (AlphabetSearch.constantBase result)) c with
      | some next => run result input fuel next
      | none => some (c.var.1.answer,
          decide (c.stk (Fin.last 12) = Alphabet.input input) &&
          decide (∀ j : Fin 12, c.stk j.castSucc = []))

def finish (result : Bool) (depth width : ℕ) : Option (Bool × Bool) :=
  let input := [true, false, true, true]
  run result input 20000 (AlphabetSearch.encoded input .dispatch (root depth width))

-- Depth-zero calls execute the concrete base subprogram and pop all six fields.
#guard finish true 0 0 == some (true, true)
#guard finish false 0 0 == some (false, true)

-- An empty midpoint has exactly one candidate, and incrementing it overflows.
#guard finish true 1 0 == some (true, true)
#guard finish false 1 0 == some (false, true)

-- Failed searches exhaust the midpoint counter; successful ones return through both halves.
#guard finish true 1 2 == some (true, true)
#guard finish false 1 2 == some (false, true)

-- Nested recursion preserves parents, clears scratch space, and preserves the input.
#guard finish true 2 1 == some (true, true)
#guard finish false 2 1 == some (false, true)


def runRuler (p : PolynomialBound) (word : List Bool) :
    ℕ → Source Bool (Ruler.Label p.degree) (Unit × Option Bool) 4 → Option Bool
  | 0, _ => none
  | fuel + 1, c =>
      match Turing.TM2.step (Ruler.program false p) c with
      | some next => runRuler p word fuel next
      | none => some (decide (∀ j : Fin 5, c.stk j =
          (![word, List.replicate (p word.length) false,
            List.replicate (word.length + 1) false, [], []] : Fin 5 → List Bool) j))

def finishRuler (p : PolynomialBound) (word : List Bool) : Option Bool :=
  runRuler p word 20000 (localConfig .copyInput () ![word, [], [], [], []])

-- Constant bounds still preserve longer inputs and the factor n + 1.
#guard finishRuler ⟨1, 0, by decide⟩ [true, false, true] == some true
-- Positive-degree rulers also handle the empty input and repeated multiplication.
#guard finishRuler ⟨2, 3, by decide⟩ [] == some true
#guard finishRuler ⟨2, 3, by decide⟩ [true, false] == some true

end SavitchMachineChecks
