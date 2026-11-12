import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Prelude
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

/-! A native finite controller writes a constant multiple of the number of
binary length digits to a separate clock tape, retaining the length counter. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.LogSeed

open BinaryCounter
set_option backward.isDefEq.respectTransparency false

abbrev Symbol := Prelude.Symbol×Option Bool

inductive Control (constant : ℕ)
  | write (initial : Bool) (position : Fin (constant+1))
  | read | advance | rewind | done
  deriving DecidableEq,Fintype

def selected {constant : ℕ} : Control constant→Fin 2
  | .write _ _ => 1
  | _ => 0

def transition {I A O : Type} (constant : ℕ) (state : Control constant)
    (_ : Option I) (_ : Option A) (_ : Option Unit) (origin : Bool) (cell : Symbol) : BankInstruction (Control constant) Symbol O :=
  match state with
  | .done => .accept
  | .write initial position =>
      if next : position.val<constant then
        .step (.write initial ⟨position.val+1,by omega⟩) (cell.1,some false) .right .stay .stay .stay none
      else .step (if initial then .read else .advance) cell .stay .stay .stay .stay none
  | .read => if (cell.1 0).isSome then .step (.write false 0) cell .stay .stay .stay .stay none
      else .step .rewind cell .stay .stay .stay .stay none
  | .advance => .step .read cell .right .stay .stay .stay none
  | .rewind => .step (if origin then .done else .rewind) cell
      (if origin then .stay else .left) .stay .stay .stay none

def bank (I A O : Type) (constant : ℕ) : TapeBank I A O (Control constant) Symbol 2 where
  initial := .write true 0
  blank := (fun _ => none,none)
  select := selected
  transition := transition constant

structure Frame where
  counterTracks : ℤ→Prelude.Symbol
  counterClock : ℤ→Option Bool
  clockTracks : ℤ→Prelude.Symbol

def counterTape (frame : Frame) (digits : List Bool) (position : ℤ) : Symbol :=
  (Function.update (frame.counterTracks position) 0 (digitTape digits position),frame.counterClock position)

def clockTape (frame : Frame) (digits : List Bool) (position : ℤ) : Symbol :=
  (frame.clockTracks position,digitTape digits position)

def encoded {O : Type} {constant : ℕ} (frame : Frame) (counter clock : List Bool)
    (counterPosition clockPosition : ℕ) (state : Control constant) : BankConfiguration O (Control constant) Symbol 2 :=
  ⟨state,0,0,0,0,[],fun index => if index=0 then counterPosition else clockPosition,
    fun index => if index=0 then counterTape frame counter else clockTape frame clock⟩

theorem two_index (index : Fin 2) : index=0 ∨ index=1 := by
  by_cases zero : index=0
  · exact Or.inl zero
  · right
    apply Fin.ext
    have bound := index.isLt
    have nonzero : index.val≠0 := by
      intro h
      exact zero (Fin.ext h)
    change index.val=1
    omega

theorem clock_write (frame : Frame) (clock : List Bool) :
    Function.update (clockTape frame clock) (clock.length : ℤ) (frame.clockTracks clock.length,some false)=
      clockTape frame (clock++[false]) := by
  have digits := digitTape_write clock [] false
  simp only [List.append_nil,List.tail_nil] at digits
  funext position
  by_cases same : position=(clock.length : ℤ)
  · subst position
    apply Prod.ext
    · simp [clockTape]
    · simpa [clockTape] using congrFun digits (clock.length : ℤ)
  · have preserved := congrFun digits position
    simpa [clockTape,Function.update_of_ne same] using congrArg (Prod.mk (frame.clockTracks position)) preserved

theorem advance_write {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A)
    (counter clock : List Bool) (counterPosition : ℕ) (initial : Bool) (position : Fin (constant+1))
    (next : Control constant) :
    (bank I A O constant).advance data (encoded frame counter clock counterPosition clock.length (.write initial position))
      next (frame.clockTracks clock.length,some false) .right .stay .stay .stay none=
      encoded frame counter (clock++[false]) counterPosition (clock.length+1) next := by
  apply BankConfiguration.ext <;> try rfl
  · funext index
    rcases two_index index with rfl | rfl <;> simp [TapeBank.advance,bank,selected,encoded,Move.onInt]
  · funext index
    rcases two_index index with rfl | rfl
    · simp [TapeBank.advance,bank,selected,encoded]
    · simpa [TapeBank.advance,bank,selected,encoded] using clock_write frame clock

theorem go {I A O : Type} (constant : ℕ) (frame : Frame) (data : InputData I A) (choices : BitString)
    (counter clock : List Bool) (counterPosition clockPosition : ℕ) (state next : Control constant)
    (table : (bank I A O constant).instruction data (encoded frame counter clock counterPosition clockPosition state)=
      .step next ((encoded (O:=O) frame counter clock counterPosition clockPosition state).tape (selected state)
        ((encoded (O:=O) frame counter clock counterPosition clockPosition state).head (selected state))) .stay .stay .stay .stay none) :
    (bank I A O constant).Steps data choices (encoded frame counter clock counterPosition clockPosition state) 1
      (encoded frame counter clock counterPosition clockPosition next) := by
  have path := TapeBank.Steps.go (bank I A O constant) data choices _ next
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) table
  exact path

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.LogSeed
