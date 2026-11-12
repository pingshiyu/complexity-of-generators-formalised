import ComplexityOfGenerators.MultitapeSpaceConstructibility
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Prelude
import ComplexityOfGenerators.Simulation.TransducerBank.BankEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.LeftBankEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.ControlEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.InputEnd

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture

open BinaryCounter

noncomputable section

inductive Phase (Q : Type) (copies : ℕ)
  | construct (state : Q)
  | zeros (next : Q) (remaining : Fin (copies+1))
  | writeLast
  | rewindClock
  | seekEnd
  | copy (state : Copy.Control)
  | rewindInput (state : InputRewind.Control)
  | done
  deriving Fintype

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

abbrev Symbol := S × (Prelude.Symbol × Option Bool)

def encodeCounter (value : Prelude.Symbol) : Symbol (S:=S) := (C.blank,(value,none))

def counter : Fin (k+2) := Fin.natAdd k 0
def clock : Fin (k+2) := Fin.natAdd k (Fin.succ (0:Fin 1))

def copyBank := BankEmbedding.bank (LeftBankEmbedding.bank (Copy.bank I A O (0:Fin 3) (2:Fin 3)) 1
  (encodeCounter C) (fun cell=>cell.2.1)) k id id

def rewindBank := BankEmbedding.bank (LeftBankEmbedding.bank (InputRewind.bank I A O (2:Fin 3)) 1
  (encodeCounter C) (fun cell=>cell.2.1)) k id id

def bank (copies : ℕ) : TapeBank I A O (Phase Q copies) (Symbol (S:=S)) (k+2) where
  initial := .construct C.initial
  blank := (C.blank,((fun _=>none),none))
  select := fun phase=> match phase with
    | .construct q=>Fin.castAdd 2 (C.select q)
    | .copy q=>(copyBank (I:=I) (A:=A) (O:=O) C).select q
    | .rewindInput q=>(rewindBank (I:=I) (A:=A) (O:=O) C).select q
    | .seekEnd | .done=>counter (k:=k)
    | _=>clock (k:=k)
  transition := fun phase input auxiliary index origin cell=>match phase with
    | .construct q=>
        match C.transition q (input.map (fun _=>())) none none origin cell.1 with
        | .accept=>.step .writeLast cell .stay .stay .stay .stay none
        | .reject | .readRandom _ _=>.reject
        | .step next write work move _ _ emit=>
            .step (if emit.isSome then .zeros next ⟨copies,by omega⟩ else .construct next)
              (write,((fun _=>none),none)) work move .stay .stay none
    | .zeros next remaining=>
        if zero : remaining.val=0 then
          .step (.construct next) cell .stay .stay .stay .stay none
        else .step (.zeros next ⟨remaining.val-1,by omega⟩)
          (C.blank,((fun _=>none),some false)) .right .stay .stay .stay none
    | .writeLast=>.step .rewindClock (C.blank,((fun _=>none),some true)) .stay .stay .stay .stay none
    | .rewindClock=>
        if origin then .step .seekEnd cell .stay .stay .stay .stay none
        else .step .rewindClock cell .left .stay .stay .stay none
    | .seekEnd=>
        if input.isSome then .step .seekEnd cell .stay .right .stay .stay none
        else .step (.copy .copy) cell .stay .stay .stay .stay none
    | .copy q=>Prelude.continueInstruction Phase.copy (.rewindInput .check) cell
        ((copyBank (I:=I) (A:=A) (O:=O) C).transition q input auxiliary index origin cell)
    | .rewindInput q=>Prelude.continueInstruction Phase.rewindInput .done cell
        ((rewindBank (I:=I) (A:=A) (O:=O) C).transition q input auxiliary index origin cell)
    | .done=>.accept

def configuration (copies : ℕ) (phase : Phase Q copies) (length temporary digits : List Bool)
    (inputPosition : ℕ) (counterPosition clockPosition : ℤ)
    (ctor : BankConfiguration Unit Q S k) : BankConfiguration O (Phase Q copies) (Symbol (S:=S)) (k+2) :=
  ⟨phase,inputPosition,0,0,0,[],Fin.addCases ctor.head (Fin.cases counterPosition (fun _=>clockPosition)),
    Fin.addCases (fun j p=>(ctor.tape j p,((fun _=>none),none)))
      (Fin.cases (fun p=>(C.blank,(Prelude.memory length temporary p,none)))
        (fun _ p=>(C.blank,((fun _=>none),digitTape digits p))))⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture
