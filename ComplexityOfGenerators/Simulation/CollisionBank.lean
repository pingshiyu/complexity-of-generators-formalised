import ComplexityOfGenerators.Simulation.TapeBankExecution
import ComplexityOfGenerators.Proofs.CollisionVerification

/-!
# The finite-control collision checker

The shared binary tape format stores each unary-index mark as `true`. At the
source-machine boundary, a present bit is decoded to `some ()`; `none` stays
blank. This internal encoding does not change the native `Unit` index alphabet.

Seven tapes hold `x`, `y`, a unary index, the two hash work tapes, and the
two hash outputs. Parsing checks canonical binary pairs, positive equal
lengths, and distinctness before either hash computation starts. Hash
instructions are simulated by finitely many tape-bank instructions.
-/

namespace ComplexityOfGenerators.Simulation

@[ext] structure CollisionCell (symbols : ℕ) where
  bit : Option Bool
  work : Option (Fin symbols)
  deriving Fintype, DecidableEq

noncomputable section
local instance : Fintype Move := Fintype.ofFinite _
set_option synthInstance.maxSize 4096

inductive CollisionPhase (states symbols : ℕ)
  | xHeader (seen : Bool)
  | xBit (seen : Bool)
  | indexBit
  | separator (seen : Bool)
  | rewindX
  | yHeader (different : Bool)
  | yBit (different : Bool)
  | storeY (bit different : Bool)
  | resetInputs (j : Fin 3)
  | hashWork (second : Bool) (q : Fin states)
  | hashInput (second : Bool) (q : Fin states) (work : Option (Fin symbols))
  | hashIndex (second : Bool) (q : Fin states) (work : Option (Fin symbols))
      (input : Option Bool) (inputOrigin : Bool)
  | moveInput (second : Bool) (q : Fin states) (write : Option (Fin symbols))
      (work input : Move) (emit : Option Bool)
  | writeWork (second : Bool) (q : Fin states) (write : Option (Fin symbols))
      (work : Move) (emit : Option Bool)
  | emit (second : Bool) (q : Fin states) (bit : Bool)
  | resetIndex
  | resetOutput (second : Bool)
  | compareLeft
  | compareRight (bit : Option Bool)
  deriving Fintype

variable (M : Machine Bool Bool Bool)

def collisionBlank : CollisionCell M.symbols := ⟨none, none⟩
def collisionBit (bit : Bool) : CollisionCell M.symbols := ⟨some bit, none⟩

def collisionSelect : CollisionPhase M.states M.symbols → Fin 7
  | .xHeader _ | .xBit _ | .separator _ | .rewindX | .yHeader _ | .yBit _ => 0
  | .storeY _ _ => 1
  | .indexBit | .resetIndex | .hashIndex .. => 2
  | .resetInputs j => j.castLE (by decide)
  | .hashWork second _ | .writeWork second .. => if second then 4 else 3
  | .hashInput second .. | .moveInput second .. => if second then 1 else 0
  | .emit second .. | .resetOutput second => if second then 6 else 5
  | .compareLeft => 5
  | .compareRight _ => 6

/-- Both boundaries of a simulated read-only tape are checked locally. -/
def collisionReadMove (origin : Bool) (symbol : Option Bool) : Move → Move
  | .left => if origin then .stay else .left
  | .stay => .stay
  | .right => if symbol.isSome then .right else .stay

def collisionTransition (q : CollisionPhase M.states M.symbols) (input : Option Bool)
    (origin : Bool) (cell : CollisionCell M.symbols) :
    BankInstruction (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) :=
  let go := fun q => BankInstruction.step q cell .stay .stay
  let rewind := fun next => BankInstruction.step (if origin then next else q) cell
    (if origin then .stay else .left) .stay
  match q with
  | .xHeader seen => match input with
    | none => .reject
    | some false => .step (.xBit seen) cell .stay .right
    | some true => .step (.separator seen) cell .stay .right
  | .xBit seen => match input with
    | none => .reject
    | some b => .step (if seen then .indexBit else .xHeader true) (collisionBit M b) .right .right
  | .indexBit => .step (.xHeader true) (collisionBit M true) .right .stay
  | .separator seen =>
      if seen && input == some false then .step .rewindX cell .stay .right else .reject
  | .rewindX => rewind (.yHeader false)
  | .yHeader different => match input with
    | some false => .step (.yBit different) cell .stay .right
    | some true => .reject
    | none => if cell.bit.isNone && different then go (.resetInputs 0) else .reject
  | .yBit different => match input, cell.bit with
    | some b, some a => .step (.storeY b (different || decide (a ≠ b))) cell .right .stay
    | _, _ => .reject
  | .storeY b different => .step (.yHeader different) (collisionBit M b) .right .right
  | .resetInputs j => rewind (if h : j = 2 then .hashWork false M.initial
      else .resetInputs ⟨j.val + 1, by omega⟩)
  | .hashWork second q => go (.hashInput second q cell.work)
  | .hashInput second q work => go (.hashIndex second q work cell.bit origin)
  | .hashIndex second q work input inputOrigin =>
      match M.transition q input none (cell.bit.map fun _ => ()) work with
      | .accept => go (if second then .resetOutput false else .resetIndex)
      | .reject | .readRandom _ _ => .reject
      | .step next write wm im _ ix emit =>
          .step (.moveInput second next write wm (collisionReadMove inputOrigin input im) emit)
            cell (collisionReadMove origin cell.bit ix) .stay
  | .moveInput second q write work im emit => .step (.writeWork second q write work emit) cell im .stay
  | .writeWork second q write work emit =>
      .step (match emit with | none => .hashWork second q | some b => .emit second q b)
        {cell with work := write.or cell.work} work .stay
  | .emit second q b => .step (.hashWork second q) (collisionBit M b) .right .stay
  | .resetIndex => rewind (.hashWork true M.initial)
  | .resetOutput second => rewind (if second then .compareLeft else .resetOutput true)
  | .compareLeft => .step (.compareRight cell.bit) cell .right .stay
  | .compareRight bit =>
      if bit = cell.bit then
        if bit.isNone then .accept else .step .compareLeft cell .right .stay
      else .reject

def collisionBank : TapeBank (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 where
  initial := .xHeader false
  blank := collisionBlank M
  select := collisionSelect M
  transition := collisionTransition M

end
end ComplexityOfGenerators.Simulation
