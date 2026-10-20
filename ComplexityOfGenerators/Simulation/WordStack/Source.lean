import ComplexityOfGenerators.Simulation.WordStack.Local
import ComplexityOfGenerators.Simulation.WordStack.WorkTape
import ComplexityOfGenerators.Foundations.ExecutionPaths

/-! A finite local interpreter for a native machine. Each interpreted step is a
fixed straight-line stack routine; random bits are read from an isolated stack. -/

namespace ComplexityOfGenerators.Simulation.WordStack.Source

inductive Status (Q : Type)
  | live (q : Q)
  | accepted
  | rejected
  | exhausted
  deriving DecidableEq, Fintype

inductive Cell (I A O Q W : Type)
  | state (q : Status Q)
  | input (a : I)
  | auxiliary (a : A)
  | work (a : Option W)
  | output (a : O)
  | bit (b : Bool)
  | unit
  deriving DecidableEq, Fintype

variable {I A O : Type} (M : Machine I A O)

abbrev Symbol := Cell I A O (Fin M.states) (Fin M.symbols)
abbrev Store := Local.Store (Symbol M) 11

@[ext] structure Snapshot where
  status : Status (Fin M.states)
  input : Zipper I
  auxiliary : Zipper A
  index : Zipper Unit
  work : Zipper (Option (Fin M.symbols))
  random : List Bool
  output : List O

namespace Snapshot

def store (c : Snapshot M) : Store M
  | 0 => [.state c.status]
  | 1 => c.input.left.map .input
  | 2 => c.input.right.map .input
  | 3 => c.auxiliary.left.map .auxiliary
  | 4 => c.auxiliary.right.map .auxiliary
  | 5 => c.index.left.map (fun _ => .unit)
  | 6 => c.index.right.map (fun _ => .unit)
  | 7 => c.work.left.map .work
  | 8 => c.work.right.map .work
  | 9 => c.random.map .bit
  | 10 => c.output.map .output

/-- The reversed output is kept on an ordinary stack. -/
def step (c : Snapshot M) : Snapshot M :=
  match c.status with
  | .live q =>
    match M.transition q c.input.read c.auxiliary.read c.index.read (c.work.read.getD none) with
    | .accept => {c with status := .accepted}
    | .reject => {c with status := .rejected}
    | .readRandom no yes => match c.random with
      | [] => {c with status := .exhausted}
      | b :: rest => {c with status := .live (if b then yes else no), random := rest}
    | .step q write wm im am nm emit =>
      {c with status := .live q
              input := c.input.clampedMove im
              auxiliary := c.auxiliary.clampedMove am
              index := c.index.clampedMove nm
              work := (match write with | none => c.work | some a => c.work.write (some a)).workMove none wm
              output := match emit with | none => c.output | some a => a :: c.output}
  | _ => c

end Snapshot

namespace Cell

def getState : Option (Symbol M) → Status (Fin M.states)
  | some (.state q) => q
  | _ => .exhausted

def getInput : Option (Symbol M) → Option I
  | some (.input a) => some a
  | _ => none

def getAuxiliary : Option (Symbol M) → Option A
  | some (.auxiliary a) => some a
  | _ => none

def getIndex : Option (Symbol M) → Option Unit
  | some .unit => some ()
  | _ => none

def getWork : Option (Symbol M) → Option (Fin M.symbols)
  | some (.work a) => a
  | _ => none

def getBit : Option (Symbol M) → Option Bool
  | some (.bit a) => some a
  | _ => none

end Cell

open Local in
def execute : ComplexityOfGenerators.Instruction O M.states M.symbols → Local (Symbol M) 11
  | .accept => write 0 (.state .accepted)
  | .reject => write 0 (.state .rejected)
  | .readRandom no yes => .read 9 fun cell => match Cell.getBit M cell with
    | none => write 0 (.state .exhausted)
    | some b => (pop 9).seq (write 0 (.state (.live (if b then yes else no))))
  | .step q w wm im am nm emit =>
    (write 0 (.state (.live q))).seq
    ((moveRead 1 2 im).seq
    ((moveRead 3 4 am).seq
    ((moveRead 5 6 nm).seq
    (((match w with | none => .skip | some a => write 8 (.work (some a))) : Local (Symbol M) 11).seq
    ((moveWork 7 8 (.work none) wm).seq
      (match emit with | none => .skip | some a => push 10 (.output a)))))))

def step : Local (Symbol M) 11 :=
  .read 0 fun state => match Cell.getState M state with
  | .live q =>
    .read 2 fun input => .read 4 fun auxiliary => .read 6 fun index => .read 8 fun work =>
      execute M (M.transition q (Cell.getInput M input) (Cell.getAuxiliary M auxiliary)
        (Cell.getIndex M index) (Cell.getWork M work))
  | _ => .skip

end ComplexityOfGenerators.Simulation.WordStack.Source
