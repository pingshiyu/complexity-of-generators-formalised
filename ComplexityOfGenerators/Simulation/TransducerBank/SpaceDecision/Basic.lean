import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.TapeCast

/-! Initialise an actual space clock, then execute an ordinary-input bank.
The source bank occupies the left lanes. Constructor and retained-length
lanes are passive during source execution; the clock is the last tape. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision

open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O QC SC QB SB : Type} {k m : ℕ}
  (constructor : TapeBank Unit Bool Unit QC SC k) (source : TapeBank I A O QB SB m)

abbrev SourceSymbol (SC SB : Type) := SC×(Prelude.Symbol×SB)
abbrev Symbol (SC SB : Type) := SourceSymbol SC SB×Option Bool
abbrev Control (QC QB : Type) (copies : ℕ) := BinaryClockInitialisation.Phase QC copies⊕BinaryClock.Control QB

def encodeSource (blank : SC) (cell : SB) : SourceSymbol SC SB := (blank,((fun _ => none),cell))
def decodeSource (cell : SourceSymbol SC SB) : SB := cell.2.2

def encodeInitial (blank : SB) (cell : BinaryClockInitialisation.Capture.Symbol (S:=SC)) : Symbol SC SB :=
  ((cell.1,(cell.2.1,blank)),cell.2.2)
def decodeInitial (cell : Symbol SC SB) : BinaryClockInitialisation.Capture.Symbol (S:=SC) :=
  (cell.1.1,(cell.1.2.1,cell.2))

def sourceBank := LeftBankEmbedding.bank source (k+1) (encodeSource constructor.blank) decodeSource

def initialBank (copies : ℕ) := BankEmbedding.bank (BinaryClockInitialisation.bank (I:=I) (A:=A) (O:=O) constructor copies)
  m (encodeInitial source.blank) decodeInitial

def clockBank := BinaryClock.bank (sourceBank constructor source)

theorem tapeCount : (m+(k+1))+1=m+(k+2) := by omega

def castClockBank := TapeCast.bank (clockBank constructor source) (tapeCount (m:=m) (k:=k))

def bank (copies : ℕ) : TapeBank I A O (Control QC QB copies) (Symbol SC SB) (m+(k+2)) where
  initial := Sum.inl (initialBank constructor source copies).initial
  blank := (initialBank constructor source copies).blank
  select := fun state => match state with
    | .inl initial => (initialBank constructor source copies).select initial
    | .inr running => (castClockBank constructor source).select running
  transition := fun state input auxiliary index origin cell => match state with
    | .inl initial => Prelude.continueInstruction Sum.inl (Sum.inr (source.initial,.check)) cell
        ((initialBank constructor source copies).transition initial input auxiliary index origin cell)
    | .inr running => ((castClockBank constructor source).transition running input auxiliary index origin cell).mapState Sum.inr

def frameHead (ctor : BankConfiguration Unit QC SC k) : Fin (k+1)→ℤ :=
  Fin.addCases ctor.head (fun _ : Fin 1 => 0)

def frameTape (length : ℕ) (ctor : BankConfiguration Unit QC SC k) : Fin (k+1)→ℤ→SourceSymbol SC SB :=
  Fin.addCases (fun tape position => (ctor.tape tape position,((fun _ => none),source.blank)))
    (fun _ position => (constructor.blank,(Prelude.memory (increment^[length] []) [] position,source.blank)))

def sourceConfiguration (length : ℕ) (ctor : BankConfiguration Unit QC SC k) :
    BankConfiguration O QB (SourceSymbol SC SB) (m+(k+1)) :=
  LeftBankEmbedding.lift (encodeSource constructor.blank) (frameHead ctor) (frameTape constructor source length ctor)
    source.initialConfiguration

def initialConfiguration (copies length : ℕ) (digits : List Bool) (ctor : BankConfiguration Unit QC SC k) :
    BankConfiguration O (Control QC QB copies) (Symbol SC SB) (m+(k+2)) :=
  (BankEmbedding.lift (encodeInitial source.blank) (fun _ : Fin m => 0)
    (fun _ _ => ((constructor.blank,((fun _ => none),source.blank)),none))
    (BinaryClockInitialisation.configuration constructor copies (.capture .done) (increment^[length] []) [] digits 0 0 0 ctor)).mapState Sum.inl

def clockConfiguration (copies length : ℕ) (digits : List Bool) (ctor : BankConfiguration Unit QC SC k) (phase : BinaryClock.Phase) :
    BankConfiguration O (Control QC QB copies) (Symbol SC SB) (m+(k+2)) :=
  (TapeCast.configuration (tapeCount (m:=m) (k:=k))
    (BinaryClock.configuration (sourceBank constructor source) digits (sourceConfiguration constructor source length ctor) phase)).mapState Sum.inr

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
