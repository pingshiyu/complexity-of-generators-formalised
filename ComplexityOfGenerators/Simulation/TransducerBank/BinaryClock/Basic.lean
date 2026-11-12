import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Frames
import ComplexityOfGenerators.Simulation.TransducerBank.BankEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.RegionEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.ControlEmbedding

/-! An actual finite binary clock on one additional work tape. A positive
clock is decremented before executing one source instruction. The source
state is retained in finite control throughout the decrement routine. -/
namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
open BinaryCounter
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ}

inductive Phase | check | counter (phase : Decrement.Control) | source
  deriving DecidableEq,Fintype

abbrev Control (Q : Type) := Q × Phase
abbrev Symbol (S : Type) := S × Option Bool

def sourceInstruction : BankInstruction Q S O → BankInstruction (Control Q) (Symbol S) O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (no,.check) (yes,.check)
  | .step next write work input auxiliary index emit =>
      .step (next,.check) (write,none) work input auxiliary index emit

def transition (source : TapeBank I A O Q S k) (state : Control Q)
    (input : Option I) (auxiliary : Option A) (index : Option Unit) (origin : Bool) (cell : Symbol S) :
    BankInstruction (Control Q) (Symbol S) O :=
  match state.2 with
  | .check => if cell.2.isNone then .reject
      else .step (state.1,.counter .borrow) cell .stay .stay .stay .stay none
  | .source => sourceInstruction (source.transition state.1 input auxiliary index origin cell.1)
  | .counter .done => .step (state.1,.source) cell .stay .stay .stay .stay none
  | .counter phase =>
      (BankEmbedding.instruction (fun bit => (source.blank,bit))
        (Decrement.transition phase input auxiliary index origin cell.2)).mapState (fun next => (state.1,.counter next))

def bank (source : TapeBank I A O Q S k) : TapeBank I A O (Control Q) (Symbol S) (k+1) where
  initial := (source.initial,.check)
  blank := (source.blank,none)
  select := fun state => match state.2 with
    | .source => Fin.castAdd 1 (source.select state.1)
    | _ => Fin.natAdd k 0
  transition := transition source

def configuration (source : TapeBank I A O Q S k) (digits : List Bool)
    (c : BankConfiguration O Q S k) (phase : Phase) : BankConfiguration O (Control Q) (Symbol S) (k+1) :=
  ⟨(c.state,phase),c.inputHead,c.auxiliaryHead,c.indexHead,c.randomHead,c.output,
    Fin.addCases c.head (fun _ => 0),
    Fin.addCases (fun j position => (c.tape j position,none)) (fun _ position => (source.blank,digitTape digits position))⟩

def context (c : BankConfiguration O Q S k) : Context O :=
  ⟨c.inputHead,c.auxiliaryHead,c.indexHead,c.randomHead,c.output⟩

theorem context_valid (source : TapeBank I A O Q S k) (data : InputData I A)
    (radius : ℕ) (c : BankConfiguration O Q S k) (bounded : source.Bounded data radius c) :
    (context c).Valid data := ⟨bounded.input,bounded.auxiliary,bounded.index⟩

theorem counter_configuration (source : TapeBank I A O Q S k) (digits : List Bool)
    (c : BankConfiguration O Q S k) (phase : Decrement.Control) :
    (BankEmbedding.lift (fun bit => (source.blank,bit)) c.head
      (fun j position => (c.tape j position,none))
      ((context c).frame (Decrement.encoded digits 0 phase))).mapState (fun next => (c.state,.counter next)) =
      configuration source digits c (.counter phase) := rfl

theorem source_instruction (source : TapeBank I A O Q S k) (data : InputData I A)
    (digits : List Bool) (c : BankConfiguration O Q S k) :
    (bank source).instruction data (configuration source digits c .source) =
      sourceInstruction (source.instruction data c) := by
  simp only [TapeBank.instruction,bank,configuration,Fin.addCases_left,transition]

theorem source_advance (source : TapeBank I A O Q S k) (data : InputData I A)
    (digits : List Bool) (c : BankConfiguration O Q S k) (next write work input auxiliary index emit) :
    (bank source).advance data (configuration source digits c .source) (next,.check) (write,none)
        work input auxiliary index emit =
      configuration source digits (source.advance data c next write work input auxiliary index emit) .check := by
  apply BankConfiguration.ext <;> try rfl
  · simp only [TapeBank.advance,bank,configuration,Fin.addCases_left,BankEmbedding.update_left]
  · simp only [TapeBank.advance,bank,configuration,Fin.addCases_left,BankEmbedding.update_left]
    congr 1
    funext j position
    by_cases same : j=source.select c.state
    · subst j
      by_cases location : position=c.head (source.select c.state)
      · subst position
        simp
      · simp [Function.update_of_ne location]
    · simp [Function.update_of_ne same]

theorem source_choose (source : TapeBank I A O Q S k) (digits : List Bool)
    (c : BankConfiguration O Q S k) (next : Q) :
    TapeBank.choose (configuration source digits c .source) (next,.check) =
      configuration source digits (TapeBank.choose c next) .check := rfl

theorem configuration_bounded (source : TapeBank I A O Q S k) (data : InputData I A)
    (digits : List Bool) (c : BankConfiguration O Q S k) (phase : Phase) (radius : ℕ)
    (bounded : source.Bounded data radius c) :
    (bank source).Bounded data radius (configuration source digits c phase) := by
  refine ⟨bounded.input,bounded.auxiliary,bounded.index,?_⟩
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa [configuration] using bounded.head j
  · simp [configuration]

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
