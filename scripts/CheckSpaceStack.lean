import ComplexityOfGenerators.Foundations.SpaceCodeBits

/-! Executable regression checks for the native-graph/library-stack connection.
Run with `lake env lean scripts/CheckSpaceStack.lean` after `lake build`.
These checks exercise the algorithm; the general proofs are in `SpaceCodeBits`.
-/

open ComplexityOfGenerators

namespace SpaceStackChecks

def accept : Machine Unit Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 1
  symbols := 0
  initial := 0
  transition := fun _ _ _ _ _ => .accept

def reject : Machine Unit Bool Unit :=
  {accept with transition := fun _ _ _ _ _ => .reject}

/-- One branch loops forever; the other accepts after reading one bit. -/
def branch : Machine Unit Bool Unit where
  inputFinite := inferInstance
  auxiliaryFinite := inferInstance
  outputFinite := inferInstance
  states := 3
  symbols := 0
  initial := 0
  transition := fun q _ _ _ _ =>
    if q = 0 then .readRandom 1 2
    else if q = 1 then .step 1 none .stay .stay .stay .stay none
    else .accept

/-- Stop at the done flag, including when the answer is false. -/
def finish (M : Machine Unit Bool Unit) (depth fuel : ℕ) : Option Bool :=
  let step := Complexity.Sav.step (M.spaceReachBase {} 0) (M.spaceAcceptBase {} 0)
    (SavitchStack.zeroCode (M.spaceCodeCodec {} 0))
  let rec go : ℕ → Complexity.Sav.Sst → Option Bool
    | 0, _ => none
    | n + 1, state => if state.done then some state.ans else go n (step state)
  go fuel (SavitchStack.initial (M.spaceCodeCodec {} 0) depth (M.initialSpaceCode {} 0))

-- Acceptance leaves inspect the current configuration; depth zero has no edge.
#guard finish accept 0 3 == some true
#guard finish reject 0 3 == some false
#guard finish branch 0 3 == some false

-- Depth one covers one edge and exercises midpoint increments and frame returns.
#guard finish accept 1 500 == some true
#guard finish reject 1 500 == some false
#guard finish branch 1 2000 == some true

-- Malformed endpoints fail; zero-cell vectors and blank-only alphabets work.
#guard accept.spaceReachBase {} 0 [] [] == false
#guard accept.spaceAcceptBase {} 0 [] == false
#guard (FixedWidthCodec.optionFin 0).decode [false] == some none
#guard (FixedWidthCodec.optionFin 0).decode [true] == none
#guard ((FixedWidthCodec.fin 0).vector 0).encode Fin.elim0 == []

end SpaceStackChecks
