import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Context
import ComplexityOfGenerators.Simulation.TransducerBank.RegionEmbedding
import ComplexityOfGenerators.Simulation.TransducerBank.RegionBounds
import ComplexityOfGenerators.MultitapeSpace

/-! An actual finite controller counts an ordinary input in binary. Its work
region is logarithmic even though it invokes the counter once per symbol. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.InputLength

set_option backward.isDefEq.respectTransparency false

inductive Control
  | check
  | counter (phase : Phase)
  deriving DecidableEq,Fintype

def embedInstruction {O : Type} : BankInstruction Phase (Option Bool) O → BankInstruction Control (Option Bool) O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (.counter no) (.counter yes)
  | .step next write work input auxiliary index emit =>
      .step (.counter next) write work input auxiliary index emit

def transition {I A O : Type} (state : Control) (input : Option I) (auxiliary : Option A)
    (index : Option Unit) (origin : Bool) (cell : Option Bool) : BankInstruction Control (Option Bool) O :=
  match state with
  | .check => if input.isSome then .step (.counter .carry) cell .stay .stay .stay .stay none else .accept
  | .counter .done => .step .check cell .stay .right .stay .stay none
  | .counter phase => embedInstruction (BinaryCounter.transition phase input auxiliary index origin cell)

def bank (I A O : Type) : TapeBank I A O Control (Option Bool) 1 where
  initial := .check
  blank := none
  select := fun _ => 0
  transition := transition

def configuration {O : Type} (digits : List Bool) (position : ℕ) (state : Control) :
    BankConfiguration O Control (Option Bool) 1 :=
  ⟨state,position,0,0,0,[],fun _ => 0,fun _ => digitTape digits⟩

theorem counter_steps {I A O : Type} (data : InputData I A) (choices : BitString)
    (digits : List Bool) (canonical : Canonical digits) (bound position : ℕ)
    (value : FixedBitBlocks.decode digits≤bound) (valid : position≤data.input.length) :
    (bank I A O).RegionSteps data choices (2*Nat.clog 2 (bound+1)+2)
      (configuration digits position (.counter .carry)) (2*(carryOffset digits+1))
      (configuration (increment digits) position (.counter .done)) := by
  have path := context_regionSteps (O:=O) data choices (Context.mk position 0 0 0 [])
    (by exact ⟨valid,Nat.zero_le _,Nat.zero_le _⟩)
    (increment_regionSteps (O:=O) data choices digits canonical bound value)
  have mapped := path.mapState (BinaryCounter.bank I A O) (bank I A O) Control.counter
    (by intro; rfl)
    (by
      intro phase input auxiliary index origin cell next write work i a x emit table
      cases phase with
      | carry => simpa only [bank,BinaryCounter.bank,transition,embedInstruction] using congrArg embedInstruction table
      | rewind => simpa only [bank,BinaryCounter.bank,transition,embedInstruction] using congrArg embedInstruction table
      | done => simp [BinaryCounter.bank,BinaryCounter.transition] at table)
    (by
      intro phase input auxiliary index origin cell no yes table
      cases phase <;> by_cases trueCell : cell=some true <;>
        simp [BinaryCounter.bank,BinaryCounter.transition,trueCell] at table)
  exact mapped

theorem bounded {I A O : Type} (data : InputData I A) (digits : List Bool) (position radius : ℕ)
    (state : Control) (valid : position≤data.input.length) :
    (bank I A O).Bounded data radius (configuration digits position state) := by
  constructor <;> simp [configuration,valid]

theorem check_step {I A O : Type} (data : InputData I A) (choices : BitString)
    (digits : List Bool) (position radius : ℕ) (present : position<data.input.length) :
    (bank I A O).RegionSteps data choices radius (configuration digits position .check) 1
      (configuration digits position (.counter .carry)) := by
  have table : (bank I A O).instruction data (configuration digits position .check)=
      .step (.counter .carry) (digitTape digits 0) .stay .stay .stay .stay none := by
    simp [TapeBank.instruction,bank,transition,configuration,List.getElem?_eq_getElem present]
  apply TapeBank.RegionSteps.step _ (.counter .carry) (digitTape digits 0) .stay .stay .stay .stay none 0 _
    (bounded data digits position radius .check (Nat.le_of_lt present)) table
  have advanced : (bank I A O).advance data (configuration digits position .check) (.counter .carry)
      (digitTape digits 0) .stay .stay .stay .stay none=configuration digits position (.counter .carry) := by
    simp [TapeBank.advance,configuration,bank,Move.onInput,Move.onInt,Nat.min_eq_left (Nat.le_of_lt present),
      Function.update_eq_self]
  rw [advanced]
  exact .refl _ (bounded data digits position radius (.counter .carry) (Nat.le_of_lt present))

theorem advance_step {I A O : Type} (data : InputData I A) (choices : BitString)
    (digits : List Bool) (position radius : ℕ) (present : position<data.input.length) :
    (bank I A O).RegionSteps data choices radius (configuration digits position (.counter .done)) 1
      (configuration digits (position+1) .check) := by
  have table : (bank I A O).instruction data (configuration digits position (.counter .done))=
      .step .check (digitTape digits 0) .stay .right .stay .stay none := rfl
  apply TapeBank.RegionSteps.step _ .check (digitTape digits 0) .stay .right .stay .stay none 0 _
    (bounded data digits position radius (.counter .done) (Nat.le_of_lt present)) table
  have advanced : (bank I A O).advance data (configuration digits position (.counter .done)) .check
      (digitTape digits 0) .stay .right .stay .stay none=configuration digits (position+1) .check := by
    simp [TapeBank.advance,configuration,bank,Move.onInput,Move.onInt,Nat.min_eq_left (by omega : position+1≤data.input.length),
      Function.update_eq_self]
  rw [advanced]
  exact .refl _ (bounded data digits (position+1) radius .check (by omega))

theorem count_prefix {I A O : Type} (data : InputData I A) (choices : BitString)
    (count : ℕ) (valid : count≤data.input.length) :
    ∃ ticks, (bank I A O).RegionSteps data choices (2*Nat.clog 2 (data.input.length+1)+2)
      (configuration [] 0 .check) ticks (configuration (increment^[count] []) count .check) := by
  induction count with
  | zero => exact ⟨0,.refl _ (bounded data [] 0 _ .check (Nat.zero_le _))⟩
  | succ count ih =>
      obtain ⟨ticks,path⟩ := ih (by omega)
      have first := check_step (O:=O) data choices (increment^[count] []) count
        (2*Nat.clog 2 (data.input.length+1)+2) (by omega)
      have middle := counter_steps (O:=O) data choices (increment^[count] []) (iterate_canonical count)
        data.input.length count (by simpa only [iterate_value] using (show count≤data.input.length by omega))
        (by omega)
      have last := advance_step (O:=O) data choices (increment (increment^[count] [])) count
        (2*Nat.clog 2 (data.input.length+1)+2) (by omega)
      refine ⟨ticks+1+2*(carryOffset (increment^[count] [])+1)+1,?_⟩
      simpa only [Function.iterate_succ_apply'] using
        ((path.trans (bank I A O) first).trans (bank I A O) middle).trans (bank I A O) last

theorem count_region {I A O : Type} (data : InputData I A) (choices : BitString) :
    (bank I A O).RegionRun data choices (2*Nat.clog 2 (data.input.length+1)+2)
      (bank I A O).initialConfiguration (.accepted []) := by
  obtain ⟨ticks,path⟩ := count_prefix (O:=O) data choices data.input.length (Nat.le_refl _)
  have initial : (bank I A O).initialConfiguration=configuration [] 0 .check := by
    apply BankConfiguration.ext <;> try rfl
    funext index position
    simp [configuration,digitTape,TapeBank.initialConfiguration,bank]
  rw [initial]
  refine ⟨ticks,configuration (increment^[data.input.length] []) data.input.length .check,path,?_⟩
  apply TapeBank.Executes.accept
  simp [TapeBank.instruction,bank,transition,configuration]

theorem count_result_value (length : ℕ) : FixedBitBlocks.decode (increment^[length] [])=length :=
  iterate_value length

theorem count_result_length (length : ℕ) : (increment^[length] []).length≤Nat.clog 2 (length+1) :=
  iterate_length length length (Nat.le_refl _)

theorem count_space {I A O : Type} (data : InputData I A) :
    (bank I A O).SpaceBound data (2*Nat.clog 2 (data.input.length+1)+2) := by
  apply TapeBank.spaceBound_of_regionRuns
  intro choices
  exact ⟨.accepted [],count_region data choices⟩

/-- The total count of visited work cells is logarithmic too; read-only
input-head movement is not charged to work space. -/
theorem count_cellSpace {I A O : Type} (data : InputData I A) :
    (bank I A O).CellSpaceBound data (4*Nat.clog 2 (data.input.length+1)+5) := by
  have counted := TapeBank.cellSpaceBound_of_radius (bank I A O) data _ (count_space data)
  convert counted using 1 <;> omega

theorem deterministic (I A O : Type) : (bank I A O).Deterministic := by
  intro state input auxiliary index origin cell
  cases state with
  | check => by_cases present : input.isSome=true <;> simp [bank,transition,present]
  | counter phase =>
      cases phase <;> by_cases trueCell : cell=some true <;>
        simp [bank,transition,BinaryCounter.transition,embedInstruction,trueCell]

theorem count_terminates_uniformly {I A O : Type} (data : InputData I A) :
    ∃ time, ∀ choices, (bank I A O).Executes data choices (bank I A O).initialConfiguration time (.accepted []) := by
  obtain ⟨time,execution⟩ := (count_region (O:=O) data []).executes (bank I A O)
  exact ⟨time,fun choices => execution.change_bits (bank I A O) (deterministic I A O) choices⟩

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.InputLength
