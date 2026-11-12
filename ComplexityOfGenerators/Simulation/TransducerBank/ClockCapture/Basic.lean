import ComplexityOfGenerators.Simulation.TransducerBank.BankEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.Fuel.Correctness

/-! A deterministic unary time constructor runs on the readonly index. Its
outputs are captured as real clock marks, and its tapes are disjoint from the
fresh source tapes. No constructor head-position convention is required. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

noncomputable section

inductive Phase (Ctor Source : Type) (copies : ℕ)
  | prefix (remaining : Fin (copies+1))
  | construct (state : Ctor)
  | append (next : Ctor) (remaining : Fin (copies+1))
  | rewind
  | source (state : Source)
  deriving Fintype

variable {O QC SC Q S : Type} {kc k : ℕ}
  (C : TapeBank Unit Bool Unit QC SC kc) (B : TapeBank Unit Bool O Q S k)

abbrev Cell := SC × (S ⊕ Unit)
abbrev Control (copies : ℕ) := Phase QC (Fuel.Phase Q S O k) copies

def encodeSource (cell : S ⊕ Unit) : Cell (SC:=SC) (S:=S) := (C.blank,cell)

def sourceBank := BankEmbedding.bank (Fuel.bank B) kc (encodeSource C) Prod.snd

def clock : Fin (kc+(k+1)) := Fin.natAdd kc (Fin.last k)

def bank (copies : ℕ) : TapeBank Unit Bool O (Control (QC:=QC) (Q:=Q) (S:=S) (O:=O) (k:=k) copies)
    (Cell (SC:=SC) (S:=S)) (kc+(k+1)) where
  initial := .prefix ⟨copies,by omega⟩
  blank := (C.blank,.inl B.blank)
  select := fun phase => match phase with
    | .construct q => Fin.castAdd (k+1) (C.select q)
    | .source q => (sourceBank C B).select q
    | _ => clock (kc:=kc) (k:=k)
  transition := fun phase input auxiliary index origin cell => match phase with
    | .prefix remaining =>
        if zero : remaining.val=0 then
          .step (.construct C.initial) cell .stay .stay .stay .stay none
        else .step (.prefix ⟨remaining.val-1,by omega⟩) (C.blank,.inr ()) .right .stay .stay .stay none
    | .construct q =>
        match C.transition q index none none origin cell.1 with
        | .accept => .step .rewind cell .stay .stay .stay .stay none
        | .reject => .reject
        | .readRandom _ _ => .reject
        | .step next write work ctorInput _ _ emit =>
            .step (if emit.isSome then .append next ⟨copies,by omega⟩ else .construct next)
              (write,.inl B.blank) work .stay .stay ctorInput none
    | .append next remaining =>
        if zero : remaining.val=0 then
          .step (.construct next) cell .stay .stay .stay .stay none
        else .step (.append next ⟨remaining.val-1,by omega⟩)
          (C.blank,.inr ()) .right .stay .stay .stay none
    | .rewind =>
        if origin then .step (.source (.fetch B.initial)) cell .stay .stay .stay .stay none
        else .step .rewind cell .left .stay .stay .left none
    | .source q =>
        match (sourceBank C B).transition q input auxiliary index origin cell with
        | .accept => .accept
        | .reject => .reject
        | .readRandom no yes => .readRandom (.source no) (.source yes)
        | .step next write work input auxiliary index emit =>
            .step (.source next) write work input auxiliary index emit

def configuration (copies : ℕ) (phase : Control (QC:=QC) (Q:=Q) (S:=S) (O:=O) (k:=k) copies)
    (fuel cursor index : ℕ) (ctor : BankConfiguration Unit QC SC kc) :
    BankConfiguration O (Control (QC:=QC) (Q:=Q) (S:=S) (O:=O) (k:=k) copies)
      (Cell (SC:=SC) (S:=S)) (kc+(k+1)) :=
  ⟨phase,0,0,index,0,[],Fin.addCases ctor.head (Fin.lastCases (cursor:ℤ) (fun _=>0)),
    Fin.addCases (fun j p=>(ctor.tape j p,.inl B.blank))
      (Fin.lastCases (fun p=>(C.blank,Fuel.clockTape B fuel p)) (fun _ _=>(C.blank,.inl B.blank)))⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
