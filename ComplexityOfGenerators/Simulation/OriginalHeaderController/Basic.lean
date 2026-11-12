import ComplexityOfGenerators.Simulation.OriginalBinarySelector.Operation
import ComplexityOfGenerators.Simulation.BoundedMachinePhase.Bounds
import ComplexityOfGenerators.Simulation.FixedBlockRetry.Execution
import ComplexityOfGenerators.Simulation.WordStack.TransferWhile
import ComplexityOfGenerators.Simulation.WordStack.OutputPrefix
import ComplexityOfGenerators.Simulation.WordStack.OutputErasure
import ComplexityOfGenerators.Simulation.WordStack.EventTrace

/-! A bounded controller selects one certified index header, then issues one
union call or two concatenation calls. An event records its source tag and
whether its index is zero; positive indices use a bounded unary export stack. -/
namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound)

abbrev Event := Bool × Bool
abbrev Cell := BoundedMachinePhase.Cell selector
abbrev Store := Local.Store (Cell selector) 35
abbrev Controller := WordStack.Routine (Cell selector) Event 35
abbrev Operation := OriginalBinarySelector.Operation

def unitSymbol : Cell selector := .unit

def phase : Controller selector :=
  (BoundedMachinePhase.phase selector width clock).mapOutput (fun tag => (tag,false))

noncomputable def retry : Command (Cell selector) Event 35 :=
  FixedBlockRetry.retryLoop (unitSymbol selector) Symbol.bit width (phase selector width clock)

def setup : Controller selector :=
  (FixedBlockRetry.setup (O := Bool) (unitSymbol selector)).mapOutput (fun tag=>(tag,false))

def boot : Command (Cell selector) Event 35 :=
  (Command.loadIndex 13 (unitSymbol selector)).seq (setup selector).command

def headerBit : Cell selector → Option Bool := UnionGenerator.outputLetter selector selector

def event (tag zero : Bool) : Command (Cell selector) Event 35 :=
  .act 0 .stay .stay (some (tag,zero))

/-- On entry, export23 has exactly the source index's number of cells. -/
def emitIndex (tag : Bool) : Command (Cell selector) Event 35 :=
  .branch 23 fun observation => if observation.1.isNone then event selector tag true
    else (Routine.ofLocal (Local.pop 23)).command.seq (event selector tag false)

def unionCalls : Command (Cell selector) Event 35 :=
  .branch 31 fun observation =>
    let tag := observation.1.bind (headerBit selector) |>.getD false
    (Routine.assign 13 23 33 (by decide) (by decide) (by decide) (fun _ => unitSymbol selector)).command.seq (emitIndex selector tag)

/-- Each certified factor header has one extra cell, including at index zero. -/
def parse (tag : Bool) : Controller selector :=
  (Routine.clear 23).seq ((Routine.transferWhile 31 23 (by decide)
    (fun cell => headerBit selector cell==some tag) (fun _ => unitSymbol selector)).seq
      (Routine.ofLocal (Local.pop 23)))

def factorCall (tag : Bool) : Command (Cell selector) Event 35 :=
  (parse selector tag).command.seq (emitIndex selector tag)

def calls : Operation → Command (Cell selector) Event 35
  | .union => unionCalls selector
  | .concatenation => (factorCall selector false).seq (factorCall selector true)

def events (operation : Operation) : Command (Cell selector) Event 35 :=
  (Routine.clear (O := Event) 0).command.seq (calls selector operation)

noncomputable def prelude : Command (Cell selector) Event 35 :=
  ((boot selector).seq (retry selector width clock)).filterMapOutput (fun _ : Event => (none : Option Event))

noncomputable def command (operation : Operation) : Command (Cell selector) Event 35 :=
  (prelude selector width clock).seq (events selector operation)
attribute [irreducible] command

def initialMemory (random : ℕ) : Memory (Cell selector) Event 35 := ⟨(),0,random,[],fun _=>[]⟩

def readyStore (n : ℕ) : Store selector :=
  Function.update (Function.update (fun _=>[]) 13 (List.replicate n (unitSymbol selector)))
    22 (List.replicate n (unitSymbol selector))

def readyMemory (n random : ℕ) : Memory (Cell selector) Event 35 := ⟨(),n,random,[],readyStore selector n⟩

def unionHeader (n : ℕ) (tag : Bool) : List (Cell selector) :=
  List.replicate (n+1) (Symbol.letter tag)
def concatHeader (left right : ℕ) : List (Cell selector) :=
  List.replicate (left+1) (Symbol.letter false)++List.replicate (right+1) (Symbol.letter true)

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
