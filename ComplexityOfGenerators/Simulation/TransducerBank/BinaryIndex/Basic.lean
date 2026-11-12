import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Prelude
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Comparison
import ComplexityOfGenerators.Simulation.TransducerBank.LeftBankEmbedding

/-! Replace a unary index of input length by binary counters on one extra
work tape. The ordinary input head remains available to a streaming matcher. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

abbrev CounterSymbol := Prelude.Symbol
abbrev WorkSymbol (S : Type) := S×CounterSymbol

inductive Control (Q : Type)
  | prepare (state : Prelude.Control)
  | probe (source : Q) (state : Comparison.Control)
  | increase (source : Q) (state : Phase)
  | decrease (source : Q) (state : Decrement.Control)
  | execute (source : Q) (live : Bool)
  deriving DecidableEq,Fintype

variable {I A O Q S : Type} {k : ℕ} (source : TapeBank I A O Q S k)

def encodeCounter (cell : CounterSymbol) : WorkSymbol S := (source.blank,cell)
def encodeSource (cell : S) : WorkSymbol S := (cell,fun _ => none)

def prepareBank := LeftBankEmbedding.bank (Prelude.bank I A O) k (encodeCounter source) Prod.snd
def probeBank := LeftBankEmbedding.bank (Comparison.bank I A O (1 : Fin 3) (0 : Fin 3)) k (encodeCounter source) Prod.snd
def increaseBank := LeftBankEmbedding.bank (Tracks.bank (BinaryCounter.bank I A O) (1 : Fin 3)) k (encodeCounter source) Prod.snd
def decreaseBank := LeftBankEmbedding.bank (Tracks.bank (Decrement.bank I A O) (1 : Fin 3)) k (encodeCounter source) Prod.snd

def probeAnswer : Comparison.Control→Bool
  | .done answer => answer
  | _ => false

def afterStep (next : Q) (live : Bool) : Move→Control Q
  | .stay => .probe next (.scan false)
  | .right => if live then .increase next .carry else .probe next (.scan false)
  | .left => .decrease next .borrow

def sourceInstruction (live : Bool) : BankInstruction Q S O→BankInstruction (Control Q) (WorkSymbol S) O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (.probe no (.scan false)) (.probe yes (.scan false))
  | .step next write work input auxiliary index emit =>
      .step (afterStep next live index) (encodeSource write) work input auxiliary .stay emit

def selected : Control Q→Fin (1+k)
  | .execute state _ => Fin.natAdd 1 (source.select state)
  | _ => Fin.castAdd k 0

def transition (state : Control Q) (input : Option I) (auxiliary : Option A)
    (index : Option Unit) (origin : Bool) (cell : WorkSymbol S) : BankInstruction (Control Q) (WorkSymbol S) O :=
  match state with
  | .prepare state => Prelude.continueInstruction Control.prepare (.probe source.initial (.scan false)) cell
      ((prepareBank source).transition state input auxiliary index origin cell)
  | .probe current state => Prelude.continueInstruction (Control.probe current) (.execute current (probeAnswer state)) cell
      ((probeBank source).transition state input auxiliary index origin cell)
  | .increase current state => Prelude.continueInstruction (Control.increase current) (.probe current (.scan false)) cell
      ((increaseBank source).transition state input auxiliary index origin cell)
  | .decrease current state => Prelude.continueInstruction (Control.decrease current) (.probe current (.scan false)) cell
      ((decreaseBank source).transition state input auxiliary index origin cell)
  | .execute current live => sourceInstruction live
      (source.transition current input auxiliary (if live then some () else none) origin cell.1)

def bank : TapeBank I A O (Control Q) (WorkSymbol S) (1+k) where
  initial := .prepare (.length .check)
  blank := encodeSource source.blank
  select := selected source
  transition := transition source

def sourceData (data : InputData I A) : InputData I A := ⟨data.input,data.auxiliary,data.input.length⟩

def counterMemory (length index : ℕ) (position : ℤ) : CounterSymbol :=
  Function.update (Function.update (fun _ => none) 0 (digitTape (increment^[length] []) position))
    1 (digitTape (increment^[index] []) position)

def configuration (length index : ℕ) (current : BankConfiguration O Q S k) (state : Control Q) :
    BankConfiguration O (Control Q) (WorkSymbol S) (1+k) :=
  ⟨state,current.inputHead,current.auxiliaryHead,0,current.randomHead,current.output,
    Fin.addCases (fun _ : Fin 1 => 0) current.head,
    Fin.addCases (fun _ position => encodeCounter source (counterMemory length index position))
      (fun tape position => encodeSource (current.tape tape position))⟩

theorem source_instruction (data : InputData I A) (current : BankConfiguration O Q S k) (live : Bool)
    (availability : live=decide (current.indexHead<data.input.length)) :
    (bank source).instruction data (configuration source data.input.length current.indexHead current (.execute current.state live))=
      sourceInstruction live (source.instruction (sourceData data) current) := by
  simp [TapeBank.instruction,bank,transition,selected,configuration,encodeSource,sourceData,availability]

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
