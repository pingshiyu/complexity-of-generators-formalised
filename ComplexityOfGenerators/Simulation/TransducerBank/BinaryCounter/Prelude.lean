import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.InputLength
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.InputRewind
import ComplexityOfGenerators.Simulation.TransducerBank.RegionEmbedding

/-! Concrete logarithmic-space preparation for a virtual unary index:
retain the input length in track 0, leave track 1 zero, and return the input
and work heads to their origins. Track 2 is a reusable empty temporary. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Prelude

set_option backward.isDefEq.respectTransparency false

abbrev Symbol := Fin 3→Option Bool

inductive Control
  | length (state : InputLength.Control)
  | copy (state : Copy.Control)
  | rewind (state : InputRewind.Control)
  | done
  deriving DecidableEq,Fintype

def continueInstruction {Q Q' S O : Type} (embed : Q→Q') (continuation : Q') (cell : S) :
    BankInstruction Q S O→BankInstruction Q' S O
  | .accept => .step continuation cell .stay .stay .stay .stay none
  | .reject => .reject
  | .readRandom no yes => .readRandom (embed no) (embed yes)
  | .step next write work input auxiliary index emit => .step (embed next) write work input auxiliary index emit

def lengthBank (I A O : Type) := Tracks.bank (InputLength.bank I A O) (0 : Fin 3)
def copyBank (I A O : Type) := Copy.bank I A O (0 : Fin 3) (2 : Fin 3)
def rewindBank (I A O : Type) := InputRewind.bank I A O (2 : Fin 3)

def transition {I A O : Type} (state : Control) (input : Option I) (auxiliary : Option A)
    (index : Option Unit) (origin : Bool) (cell : Symbol) : BankInstruction Control Symbol O :=
  match state with
  | .done => .accept
  | .length state => continueInstruction Control.length (.copy .copy) cell
      ((lengthBank I A O).transition state input auxiliary index origin cell)
  | .copy state => continueInstruction Control.copy (.rewind .check) cell
      ((copyBank I A O).transition state input auxiliary index origin cell)
  | .rewind state => continueInstruction Control.rewind .done cell
      ((rewindBank I A O).transition state input auxiliary index origin cell)

def bank (I A O : Type) : TapeBank I A O Control Symbol 1 where
  initial := .length .check
  blank := fun _ => none
  select := fun _ => 0
  transition := transition

def memory (length temporary : List Bool) (position : ℤ) : Symbol :=
  Function.update (Function.update (fun _ => none) 0 (digitTape length position)) 2 (digitTape temporary position)

def configuration {O : Type} (length temporary : List Bool) (inputPosition : ℕ) (state : Control) :
    BankConfiguration O Control Symbol 1 :=
  ⟨state,inputPosition,0,0,0,[],fun _ => 0,fun _ => memory length temporary⟩

theorem memory_empty_temporary (length : List Bool) (position : ℤ) :
    memory length [] position=Function.update (fun _ : Fin 3 => none) 0 (digitTape length position) := by
  change Function.update (Function.update (fun _ : Fin 3 => none) 0 (digitTape length position)) 2 (digitTape [] position)=_
  have empty : digitTape [] position=none := by simp [digitTape]
  rw [empty]
  have second : (Function.update (fun _ : Fin 3 => none) 0 (digitTape length position)) 2=none := by simp
  rw [← second]
  exact Function.update_eq_self _ _

theorem memory_empty_temporary_function (length : List Bool) :
    memory length []=fun position => Function.update (fun _ : Fin 3 => none) 0 (digitTape length position) := by
  funext position
  exact memory_empty_temporary length position

theorem bounded {I A O : Type} (data : InputData I A) (length temporary : List Bool)
    (inputPosition radius : ℕ) (state : Control) (valid : inputPosition≤data.input.length) :
    (bank I A O).Bounded data radius (configuration length temporary inputPosition state) := by
  constructor <;> simp [configuration,valid]

theorem go {I A O : Type} (data : InputData I A) (choices : BitString) (length temporary : List Bool)
    (inputPosition radius : ℕ) (state next : Control) (valid : inputPosition≤data.input.length)
    (table : (bank I A O).instruction data (configuration length temporary inputPosition state)=
      .step next (memory length temporary 0) .stay .stay .stay .stay none) :
    (bank I A O).RegionSteps data choices radius (configuration length temporary inputPosition state) 1
      (configuration length temporary inputPosition next) := by
  apply TapeBank.RegionSteps.step _ next _ .stay .stay .stay .stay none 0 _
    (bounded data length temporary inputPosition radius state valid) table
  have advanced : (bank I A O).advance data (configuration length temporary inputPosition state) next
      (memory length temporary 0) .stay .stay .stay .stay none=configuration length temporary inputPosition next := by
    simp [TapeBank.advance,configuration,bank,Move.onInt,Move.onInput,Nat.min_eq_left valid,Function.update_eq_self]
  rw [advanced]
  exact .refl _ (bounded data length temporary inputPosition radius next valid)

theorem length_steps {I A O : Type} (data : InputData I A) (choices : BitString) :
    ∃ time, (bank I A O).RegionSteps data choices (2*Nat.clog 2 (data.input.length+1)+2)
      (configuration [] [] 0 (.length .check)) time
      (configuration (increment^[data.input.length] []) [] data.input.length (.length .check)) := by
  obtain ⟨time,path⟩ := InputLength.count_prefix (O:=O) data choices data.input.length (Nat.le_refl _)
  have lifted := Tracks.regionSteps_lift (InputLength.bank I A O) (0 : Fin 3) (fun _ _ _ => none) path
  have mapped := lifted.mapState (lengthBank I A O) (bank I A O) Control.length
    (by intro;rfl)
    (by
      intro state input auxiliary index origin cell next write work i a x emit table
      simpa only [bank,transition,continueInstruction] using
        congrArg (continueInstruction Control.length (.copy .copy) cell) table)
    (by
      intro state input auxiliary index origin cell no yes table
      simpa only [bank,transition,continueInstruction] using
        congrArg (continueInstruction Control.length (.copy .copy) cell) table)
  refine ⟨time,?_⟩
  simpa only [configuration,Tracks.lift,InputLength.configuration,BankConfiguration.mapState,memory_empty_temporary_function] using mapped

theorem copy_steps {I A O : Type} (data : InputData I A) (choices : BitString) :
    (bank I A O).RegionSteps data choices (2*Nat.clog 2 (data.input.length+1)+2)
      (configuration (increment^[data.input.length] []) [] data.input.length (.copy .copy))
      (2*((increment^[data.input.length] []).length+1))
      (configuration (increment^[data.input.length] []) (increment^[data.input.length] []) data.input.length (.copy .done)) := by
  have path := copy_framed (O:=O) (0 : Fin 3) (2 : Fin 3) (by decide) (fun _ _ => none) data choices
    (Context.mk data.input.length 0 0 0 []) (by exact ⟨le_rfl,Nat.zero_le _,Nat.zero_le _⟩)
    (increment^[data.input.length] []) (iterate_canonical _) data.input.length (by simp [iterate_value])
  have mapped := path.mapState (copyBank I A O) (bank I A O) Control.copy
    (by intro;rfl)
    (by
      intro state input auxiliary index origin cell next write work i a x emit table
      simpa only [bank,transition,continueInstruction] using
        congrArg (continueInstruction Control.copy (.rewind .check) cell) table)
    (by
      intro state input auxiliary index origin cell no yes table
      simpa only [bank,transition,continueInstruction] using
        congrArg (continueInstruction Control.copy (.rewind .check) cell) table)
  exact mapped

theorem rewind_steps {I A O : Type} (data : InputData I A) (choices : BitString) :
    ∃ time, (bank I A O).RegionSteps data choices (2*Nat.clog 2 (data.input.length+1)+4)
      (configuration (increment^[data.input.length] []) (increment^[data.input.length] []) data.input.length (.rewind .check)) time
      (configuration (increment^[data.input.length] []) [] 0 (.rewind .check)) := by
  obtain ⟨time,path⟩ := InputRewind.rewind_steps (O:=O) (2 : Fin 3)
    (fun position => Function.update (fun _ => none) 0 (digitTape (increment^[data.input.length] []) position))
    data choices data.input.length data.input.length le_rfl le_rfl
  have mapped := path.mapState (rewindBank I A O) (bank I A O) Control.rewind
    (by intro;rfl)
    (by
      intro state input auxiliary index origin cell next write work i a x emit table
      simpa only [bank,transition,continueInstruction] using
        congrArg (continueInstruction Control.rewind .done cell) table)
    (by
      intro state input auxiliary index origin cell no yes table
      simpa only [bank,transition,continueInstruction] using
        congrArg (continueInstruction Control.rewind .done cell) table)
  exact ⟨time,mapped⟩

theorem prepared_steps {I A O : Type} (data : InputData I A) (choices : BitString) :
    ∃ time, (bank I A O).RegionSteps data choices (2*Nat.clog 2 (data.input.length+1)+4)
      (bank I A O).initialConfiguration time (configuration (increment^[data.input.length] []) [] 0 .done) := by
  obtain ⟨lengthTime,lengthPath⟩ := length_steps (O:=O) data choices
  have toCopy := go (O:=O) data choices (increment^[data.input.length] []) [] data.input.length
    (2*Nat.clog 2 (data.input.length+1)+4) (.length .check) (.copy .copy) le_rfl (by
      simp [TapeBank.instruction,bank,transition,lengthBank,Tracks.bank,InputLength.bank,InputLength.transition,
        Tracks.instruction,continueInstruction,configuration])
  have copying := (copy_steps (O:=O) data choices).mono
    (s:=2*Nat.clog 2 (data.input.length+1)+4) (bank I A O) (by omega)
  have toRewind := go (O:=O) data choices (increment^[data.input.length] []) (increment^[data.input.length] []) data.input.length
    (2*Nat.clog 2 (data.input.length+1)+4) (.copy .done) (.rewind .check) le_rfl rfl
  obtain ⟨rewindTime,rewinding⟩ := rewind_steps (O:=O) data choices
  have finish := go (O:=O) data choices (increment^[data.input.length] []) [] 0
    (2*Nat.clog 2 (data.input.length+1)+4) (.rewind .check) .done (Nat.zero_le _) (by
      simp [TapeBank.instruction,bank,transition,rewindBank,InputRewind.bank,InputRewind.transition,
        continueInstruction,configuration,memory,digitTape])
  have all := (((((lengthPath.mono (s:=2*Nat.clog 2 (data.input.length+1)+4) (bank I A O) (by omega)).trans
    (bank I A O) toCopy).trans (bank I A O) copying).trans
    (bank I A O) toRewind).trans (bank I A O) rewinding).trans (bank I A O) finish
  have initial : (bank I A O).initialConfiguration=configuration [] [] 0 (.length .check) := by
    apply BankConfiguration.ext <;> try rfl
    funext tape position chosen
    simp [TapeBank.initialConfiguration,bank,configuration,memory,digitTape]
  refine ⟨lengthTime+1+2*((increment^[data.input.length] []).length+1)+1+rewindTime+1,?_⟩
  rw [initial]
  exact all

theorem prepared_region {I A O : Type} (data : InputData I A) (choices : BitString) :
    (bank I A O).RegionRun data choices (2*Nat.clog 2 (data.input.length+1)+4)
      (bank I A O).initialConfiguration (.accepted []) := by
  obtain ⟨time,path⟩ := prepared_steps (O:=O) data choices
  refine ⟨time,configuration (increment^[data.input.length] []) [] 0 .done,path,?_⟩
  apply TapeBank.Executes.accept
  rfl

theorem prepared_space {I A O : Type} (data : InputData I A) :
    (bank I A O).SpaceBound data (2*Nat.clog 2 (data.input.length+1)+4) := by
  apply TapeBank.spaceBound_of_regionRuns
  intro choices
  exact ⟨.accepted [],prepared_region data choices⟩

theorem prepared_cellSpace {I A O : Type} (data : InputData I A) :
    (bank I A O).CellSpaceBound data (4*Nat.clog 2 (data.input.length+1)+9) := by
  have counted := TapeBank.cellSpaceBound_of_radius (bank I A O) data _ (prepared_space data)
  convert counted using 1 <;> omega

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Prelude
