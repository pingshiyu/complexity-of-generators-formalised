import ComplexityOfGenerators.Simulation.WordStack.BoundedInput
import ComplexityOfGenerators.Simulation.WordStack.Output

/-! A bounded two-source controller used for binary union. -/
namespace ComplexityOfGenerators.Simulation.UnionGenerator

open WordStack

inductive Symbol (α : Type) (G H : Machine Unit Bool α)
  | letter (a : α)
  | bit (b : Bool)
  | unit
  | left (cell : Source.Symbol G)
  | right (cell : Source.Symbol H)
  deriving Fintype

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

abbrev Cell := Symbol α G H
abbrev Store := Local.Store (Cell G H) 35
abbrev Controller := WordStack.Routine (Cell G H) α 35

def letters (word : List α) : List (Cell G H) := word.map Symbol.letter

def held : Option (List α) → List (Cell G H)
  | none => []
  | some word => letters G H word

def flagWord (value : Bool) : List (Cell G H) := if value then [.unit] else []

def flag (reg : Fin 35) (value : Bool) : Controller G H :=
  (WordStack.Routine.clear reg).seq (if value then WordStack.Routine.ofLocal (Local.push reg .unit) else WordStack.Routine.skip)

def takeOutput (destination : Fin 35) (different : (10 : Fin 35) ≠ destination)
    (map : Cell G H → Cell G H) : Controller G H :=
  (WordStack.Routine.clear destination).seq (WordStack.Routine.transfer 10 destination different map)

def leftDecode : Cell G H → Source.Symbol G
  | .left cell => cell
  | _ => .unit

def rightDecode : Cell G H → Source.Symbol H
  | .right cell => cell
  | _ => .unit

def leftBit : Cell G H → Cell G H
  | .bit b => .left (.bit b)
  | _ => .left (.bit false)

def rightBit : Cell G H → Cell G H
  | .bit b => .right (.bit b)
  | _ => .right (.bit false)

def leftOutput : Cell G H → Cell G H
  | .left (.output a) => .letter a
  | _ => .unit

def rightOutput : Cell G H → Cell G H
  | .right (.output a) => .letter a
  | _ => .unit

noncomputable def leftTrial (seed time : PolynomialBound) : Controller G H :=
  BoundedSource.sourceTrial .unit Symbol.bit G Symbol.left (leftDecode G H)
    (fun _ => .left .unit) (fun _ => .left .unit) (leftBit G H) seed time

noncomputable def rightTrial (seed time : PolynomialBound) : Controller G H :=
  BoundedSource.sourceTrial .unit Symbol.bit H Symbol.right (rightDecode G H)
    (fun _ => .right .unit) (fun _ => .right .unit) (rightBit G H) seed time

def leftFinish : Controller G H :=
  WordStack.Routine.branch 0 fun status => match status with
    | some (.left (.state .accepted)) =>
      (takeOutput G H 25 (by decide) (leftOutput G H)).seq (flag G H 27 true)
    | _ => (WordStack.Routine.clear 25).seq (flag G H 27 false)

def rightFinish : Controller G H :=
  WordStack.Routine.branch 0 fun status => match status with
    | some (.right (.state .accepted)) =>
      (takeOutput G H 26 (by decide) (rightOutput G H)).seq (flag G H 28 true)
    | _ => (WordStack.Routine.clear 26).seq (flag G H 28 false)

def chooseFrom (first second firstFlag secondFlag : Fin 35)
    (firstDifferent : first ≠ 11 ∧ first ≠ 33)
    (secondDifferent : second ≠ 11 ∧ second ≠ 33) : Controller G H :=
  WordStack.Routine.branch firstFlag fun available => if available.isSome then
    (WordStack.Routine.assign first 11 33 firstDifferent.1 firstDifferent.2 (by decide) id).seq (flag G H 29 true)
  else WordStack.Routine.branch secondFlag fun available => if available.isSome then
    (WordStack.Routine.assign second 11 33 secondDifferent.1 secondDifferent.2 (by decide) id).seq (flag G H 29 true)
  else (WordStack.Routine.clear 11).seq (flag G H 29 false)

def choose : Controller G H :=
  WordStack.Routine.branch 17 fun coin => match coin with
    | some (.bit true) => chooseFrom G H 26 25 28 27 (by decide) (by decide)
    | _ => chooseFrom G H 25 26 27 28 (by decide) (by decide)

noncomputable def body (leftSeed leftTime rightSeed rightTime : PolynomialBound) : Controller G H :=
  (leftTrial G H leftSeed leftTime).seq
  ((leftFinish G H).seq
  ((rightTrial G H rightSeed rightTime).seq
  ((rightFinish G H).seq (choose G H))))

def outputLetter : Cell G H → Option α
  | .letter a => some a
  | _ => none

def finish : Command (Cell G H) α 35 :=
  .branch 29 fun available => if available.1.isSome then
    Command.emitWord 11 (outputLetter G H) else .drain

noncomputable def command (leftSeed leftTime rightSeed rightTime seed : PolynomialBound) :
    Command (Cell G H) α 35 :=
  (BoundedSource.prepareCommand .unit Symbol.bit seed).seq
    ((body G H leftSeed leftTime rightSeed rightTime).command.seq (finish G H))

/-- The actual bounded run of one source, interpreted as an optional result. -/
def sourceValue (M : Machine Unit Bool α) (time : PolynomialBound) (n : ℕ) (bits : BitString) :
    Option (List α) :=
  (M.run (generatorData n) bits (time n)).acceptedWord

/-- Blocks for both source calls precede the selector. Failed source calls are
ignored; the other successful call supplies the result. -/
def value (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) (bits : BitString) :
    Option (List α) :=
  let left := sourceValue G leftTime n (bits.take (leftSeed n))
  let right := sourceValue H rightTime n ((bits.drop (leftSeed n)).take (rightSeed n))
  if (bits.drop (leftSeed n + rightSeed n)).head? = some true then right.or left else left.or right

end ComplexityOfGenerators.Simulation.UnionGenerator
