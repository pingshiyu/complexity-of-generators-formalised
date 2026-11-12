import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Tape
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Copy

set_option backward.isDefEq.respectTransparency false

inductive Control | copy | rewind | done
  deriving DecidableEq,Fintype

def transition {I A O : Type} {tracks : ℕ} (fromTrack target : Fin tracks) (state : Control)
    (_ : Option I) (_ : Option A) (_ : Option Unit) (origin : Bool) (cell : Fin tracks→Option Bool) :
    BankInstruction Control (Fin tracks→Option Bool) O :=
  match state with
  | .done => .accept
  | .copy => match cell fromTrack with
      | none => .step .rewind cell .stay .stay .stay .stay none
      | some bit => .step .copy (Function.update cell target (some bit)) .right .stay .stay .stay none
  | .rewind => .step (if origin then .done else .rewind) cell
      (if origin then .stay else .left) .stay .stay .stay none

def bank (I A O : Type) {tracks : ℕ} (fromTrack target : Fin tracks) :
    TapeBank I A O Control (Fin tracks→Option Bool) 1 where
  initial := .copy
  blank := fun _ => none
  select := fun _ => 0
  transition := transition fromTrack target

def memory {tracks : ℕ} (fromTrack target : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (source destination : List Bool) (position : ℤ) : Fin tracks→Option Bool :=
  Function.update (Function.update (other position) fromTrack (digitTape source position)) target
    (digitTape destination position)

def encoded {O : Type} {tracks : ℕ} (fromTrack target : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (source destination : List Bool) (position : ℕ) (state : Control) :
    BankConfiguration O Control (Fin tracks→Option Bool) 1 :=
  ⟨state,0,0,0,0,[],fun _ => position,fun _ => memory fromTrack target other source destination⟩

theorem read_source {tracks : ℕ} (fromTrack target : Fin tracks) (different : fromTrack≠target)
    (other : ℤ→Fin tracks→Option Bool) (source destination : List Bool) (position : ℤ) :
    memory fromTrack target other source destination position fromTrack=digitTape source position := by
  simp [memory,Function.update_of_ne different]

theorem write_destination {tracks : ℕ} (fromTrack target : Fin tracks)
    (other : ℤ→Fin tracks→Option Bool) (source low : List Bool) (bit : Bool) :
    Function.update (memory fromTrack target other source low) (low.length : ℤ)
        (Function.update (memory fromTrack target other source low low.length) target (some bit))=
      memory fromTrack target other source (low++[bit]) := by
  have digit := digitTape_write low [] bit
  simp only [List.append_nil,List.tail_nil] at digit
  funext position chosen
  by_cases samePosition : position=(low.length : ℤ)
  · subst position
    by_cases sameTrack : chosen=target
    · subst chosen
      simpa [memory] using congrFun digit (low.length : ℤ)
    · simp [memory,Function.update_of_ne sameTrack]
  · have preserved : digitTape low position=digitTape (low++[bit]) position := by
      simpa only [Function.update_of_ne samePosition] using congrFun digit position
    simp [Function.update_of_ne samePosition,memory,preserved]

theorem advance_copy {I A O : Type} {tracks : ℕ} (fromTrack target : Fin tracks)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (source low : List Bool) (bit : Bool) :
    (bank I A O fromTrack target).advance data (encoded fromTrack target other source low low.length .copy) .copy
      (Function.update (memory fromTrack target other source low low.length) target (some bit))
      .right .stay .stay .stay none=
      encoded fromTrack target other source (low++[bit]) (low.length+1) .copy := by
  apply BankConfiguration.ext <;> try rfl
  · funext index
    rw [one_index index]
    simp [TapeBank.advance,encoded,bank,Move.onInt]
  · funext index
    rw [one_index index]
    simpa [TapeBank.advance,encoded,bank] using write_destination fromTrack target other source low bit

theorem copy_steps {I A O : Type} {tracks : ℕ} (fromTrack target : Fin tracks) (different : fromTrack≠target)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString) (low high : List Bool) :
    (bank I A O fromTrack target).Steps data choices (encoded fromTrack target other (low++high) low low.length .copy)
      (high.length+1) (encoded fromTrack target other (low++high) (low++high) (low++high).length .rewind) := by
  induction high generalizing low with
  | nil =>
      have table : (bank I A O fromTrack target).instruction data (encoded fromTrack target other (low++[]) low low.length .copy)=
          .step .rewind (memory fromTrack target other (low++[]) low low.length) .stay .stay .stay .stay none := by
        simp [TapeBank.instruction,bank,transition,encoded,read_source fromTrack target different,digitTape]
      have path := TapeBank.Steps.go (bank I A O fromTrack target) data choices _ .rewind
        (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _) table
      simpa [encoded] using path
  | cons bit rest ih =>
      have table : (bank I A O fromTrack target).instruction data (encoded fromTrack target other (low++bit::rest) low low.length .copy)=
          .step .copy (Function.update (memory fromTrack target other (low++bit::rest) low low.length) target (some bit))
            .right .stay .stay .stay none := by
        simp [TapeBank.instruction,bank,transition,encoded,read_source fromTrack target different,digitTape_at]
      have path := TapeBank.Steps.single (bank I A O fromTrack target) data choices _ _ _ _ _ _ _ _ table
      rw [advance_copy] at path
      have remaining := ih (low++[bit])
      have aligned : (bank I A O fromTrack target).Steps data choices
          (encoded fromTrack target other (low++bit::rest) (low++[bit]) (low.length+1) .copy) (rest.length+1)
          (encoded fromTrack target other (low++bit::rest) (low++bit::rest) (low++bit::rest).length .rewind) := by
        simpa [List.append_assoc] using remaining
      simpa [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using path.trans (bank I A O fromTrack target) aligned

/-- Copy to an empty temporary track. The source and all other tracks are
preserved; the physical head returns to the common origin. -/
theorem routine_steps {I A O : Type} {tracks : ℕ} (fromTrack target : Fin tracks) (different : fromTrack≠target)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString) (digits : List Bool) :
    (bank I A O fromTrack target).Steps data choices (encoded fromTrack target other digits [] 0 .copy) (2*(digits.length+1))
      (encoded fromTrack target other digits digits 0 .done) := by
  have copied : (bank I A O fromTrack target).Steps data choices (encoded fromTrack target other digits [] 0 .copy)
      (digits.length+1) (encoded fromTrack target other digits digits digits.length .rewind) := by
    simpa using copy_steps fromTrack target different other data choices [] digits
  have back := TapeBank.rewind_steps (bank I A O fromTrack target) data choices .rewind .done 0 rfl
    (by intro input auxiliary index origin cell;rfl) digits.length
    (encoded fromTrack target other digits digits digits.length .rewind) rfl rfl
    (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
  have aligned : (bank I A O fromTrack target).Steps data choices (encoded fromTrack target other digits digits digits.length .rewind)
      (digits.length+1) (encoded fromTrack target other digits digits 0 .done) := by
    convert back using 1
    apply BankConfiguration.ext <;> try rfl
    funext index
    rw [one_index index]
    rfl
  convert copied.trans (bank I A O fromTrack target) aligned using 1 <;> omega

theorem routine_regionSteps {I A O : Type} {tracks : ℕ} (fromTrack target : Fin tracks) (different : fromTrack≠target)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (canonical : Canonical digits) (bound : ℕ) (value : FixedBitBlocks.decode digits≤bound) :
    (bank I A O fromTrack target).RegionSteps data choices (2*Nat.clog 2 (bound+1)+2)
      (encoded fromTrack target other digits [] 0 .copy) (2*(digits.length+1))
      (encoded fromTrack target other digits digits 0 .done) := by
  have length := canonical_length_bound digits canonical (Nat.clog 2 (bound+1)) (by
    have power := Nat.le_pow_clog (by decide : 1<2) (bound+1)
    omega)
  have initial : (bank I A O fromTrack target).Bounded data 0 (encoded fromTrack target other digits [] 0 .copy) := by
    constructor <;> simp [encoded]
  exact ((routine_steps fromTrack target different other data choices digits).inRegion (bank I A O fromTrack target) 0 initial).mono
    (bank I A O fromTrack target) (by omega)

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Copy
