import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.LogSeedSteps

/-! Complete finite control for a binary clock initialiser. The retained input
length is computed first, its bit width seeds the zero digits, and an actual
unary space constructor supplies the remaining digits. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation

open BinaryCounter
noncomputable section

inductive Phase (Q : Type) (copies : ℕ)
  | prelude (state : Prelude.Control)
  | seed (state : LogSeed.Control copies)
  | capture (state : Capture.Phase Q copies)
  deriving Fintype

variable {I A O Q S : Type} {k : ℕ} (C : TapeBank Unit Bool Unit Q S k)

def preludeBank := BankEmbedding.bank (LeftBankEmbedding.bank (Prelude.bank I A O) 1
  (Capture.encodeCounter C) (fun cell=>cell.2.1)) k id id

def seedBank (copies : ℕ) := BankEmbedding.bank (LogSeed.bank I A O copies) k
  (fun value=>(C.blank,value)) Prod.snd

def bank (copies : ℕ) : TapeBank I A O (Phase Q copies) (Capture.Symbol (S:=S)) (k+2) where
  initial := .prelude (Prelude.bank I A O).initial
  blank := (C.blank,((fun _=>none),none))
  select := fun phase=>match phase with
    | .prelude q=>(preludeBank (I:=I) (A:=A) (O:=O) C).select q
    | .seed q=>(seedBank (I:=I) (A:=A) (O:=O) C copies).select q
    | .capture q=>(Capture.bank (I:=I) (A:=A) (O:=O) C copies).select q
  transition := fun phase input auxiliary index origin cell=>match phase with
    | .prelude q=>Prelude.continueInstruction Phase.prelude (.seed (.write true 0)) cell
        ((preludeBank (I:=I) (A:=A) (O:=O) C).transition q input auxiliary index origin cell)
    | .seed q=>Prelude.continueInstruction Phase.seed (.capture (.construct C.initial)) cell
        ((seedBank (I:=I) (A:=A) (O:=O) C copies).transition q input auxiliary index origin cell)
    | .capture q=>((Capture.bank (I:=I) (A:=A) (O:=O) C copies).transition q input auxiliary index origin cell).mapState Phase.capture

def configuration (copies : ℕ) (phase : Phase Q copies) (length temporary digits : List Bool)
    (inputPosition : ℕ) (counterPosition clockPosition : ℤ) (ctor : BankConfiguration Unit Q S k) :
    BankConfiguration O (Phase Q copies) (Capture.Symbol (S:=S)) (k+2) :=
  (Capture.configuration C copies .done length temporary digits inputPosition counterPosition clockPosition ctor).mapState (fun _=>phase)

 theorem configuration_capture (copies : ℕ) (phase : Capture.Phase Q copies) (length temporary digits : List Bool)
    (inputPosition : ℕ) (counterPosition clockPosition : ℤ) (ctor : BankConfiguration Unit Q S k) :
    configuration (O:=O) C copies (.capture phase) length temporary digits inputPosition counterPosition clockPosition ctor=
      (Capture.configuration C copies phase length temporary digits inputPosition counterPosition clockPosition ctor).mapState Phase.capture := rfl

end
end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation
