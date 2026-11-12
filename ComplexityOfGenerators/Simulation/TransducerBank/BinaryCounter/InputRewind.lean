import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Frames
import ComplexityOfGenerators.Simulation.TransducerBank.RegionEmbedding

/-! Rewind an ordinary input head using a binary temporary counter. Each
decrement returns the work head to its origin, so all iterations reuse one
logarithmic region. Other counter tracks are preserved. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.InputRewind

set_option backward.isDefEq.respectTransparency false

inductive Control | check | counter (state : Decrement.Control)
  deriving DecidableEq,Fintype

def embedInstruction {S O : Type} : BankInstruction Decrement.Control S O → BankInstruction Control S O
  | .accept => .accept
  | .reject => .reject
  | .readRandom no yes => .readRandom (.counter no) (.counter yes)
  | .step next write work input auxiliary index emit =>
      .step (.counter next) write work input auxiliary index emit

def transition {I A O : Type} {tracks : ℕ} (track : Fin tracks) (state : Control)
    (input : Option I) (auxiliary : Option A) (index : Option Unit) (origin : Bool) (cell : Fin tracks→Option Bool) :
    BankInstruction Control (Fin tracks→Option Bool) O :=
  match state with
  | .check => if (cell track).isSome then .step (.counter .borrow) cell .stay .stay .stay .stay none else .accept
  | .counter .done => .step .check cell .stay .left .stay .stay none
  | .counter state => embedInstruction ((Tracks.bank (Decrement.bank I A O) track).transition state input auxiliary index origin cell)

def bank (I A O : Type) {tracks : ℕ} (track : Fin tracks) : TapeBank I A O Control (Fin tracks→Option Bool) 1 where
  initial := .check
  blank := fun _ => none
  select := fun _ => 0
  transition := transition track

def configuration {O : Type} {tracks : ℕ} (track : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (bits : List Bool) (inputPosition : ℕ) (state : Control) : BankConfiguration O Control (Fin tracks→Option Bool) 1 :=
  ⟨state,inputPosition,0,0,0,[],fun _ => 0,
    fun _ position => Function.update (other position) track (digitTape bits position)⟩

theorem bounded {I A O : Type} {tracks : ℕ} (track : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (data : InputData I A) (bits : List Bool) (inputPosition radius : ℕ) (state : Control)
    (valid : inputPosition≤data.input.length) :
    (bank I A O track).Bounded data radius (configuration track other bits inputPosition state) := by
  constructor <;> simp [configuration,valid]

theorem decrement_steps {I A O : Type} {tracks : ℕ} (track : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (data : InputData I A) (choices : BitString) (bits : List Bool) (canonical : Canonical bits)
    (bound inputPosition : ℕ) (value : FixedBitBlocks.decode bits≤bound) (valid : inputPosition≤data.input.length) :
    ∃ time, (bank I A O track).RegionSteps data choices (2*Nat.clog 2 (bound+1)+4)
      (configuration track other bits inputPosition (.counter .borrow)) time
      (configuration track other (decrement bits) inputPosition (.counter .done)) := by
  obtain ⟨time,path⟩ := Decrement.decrement_regionSteps (O:=O) data choices bits canonical bound value
  have lifted := Tracks.regionSteps_lift (Decrement.bank I A O) track (fun _ => other) path
  have framed := Context.regionSteps_frame (Tracks.bank (Decrement.bank I A O) track)
    (Tracks.workOnly _ _ (Decrement.workOnly I A O)) data choices (Context.mk inputPosition 0 0 0 [])
    (by exact ⟨valid,Nat.zero_le _,Nat.zero_le _⟩) lifted
  have mapped := framed.mapState (Tracks.bank (Decrement.bank I A O) track) (bank I A O track) Control.counter
    (by intro;rfl)
    (by
      intro state input auxiliary index origin cell next write work i a x emit table
      cases state with
      | done => simp [Tracks.bank,Decrement.bank,Decrement.transition,Tracks.instruction] at table
      | borrow => simpa only [bank,transition,embedInstruction] using congrArg embedInstruction table
      | inspect => simpa only [bank,transition,embedInstruction] using congrArg embedInstruction table
      | erase => simpa only [bank,transition,embedInstruction] using congrArg embedInstruction table
      | rewind => simpa only [bank,transition,embedInstruction] using congrArg embedInstruction table)
    (by
      intro state input auxiliary index origin cell no yes table
      have silent := (Tracks.workOnly _ track (Decrement.workOnly I A O)).silent state input auxiliary index origin cell
      simp [table] at silent)
  exact ⟨time,mapped⟩

theorem check_step {I A O : Type} {tracks : ℕ} (track : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (data : InputData I A) (choices : BitString) (bits : List Bool) (nonempty : bits≠[])
    (inputPosition radius : ℕ) (valid : inputPosition≤data.input.length) :
    (bank I A O track).RegionSteps data choices radius (configuration track other bits inputPosition .check) 1
      (configuration track other bits inputPosition (.counter .borrow)) := by
  have head : (digitTape bits 0).isSome=true := by cases bits <;> simp_all [digitTape]
  have table : (bank I A O track).instruction data (configuration track other bits inputPosition .check)=
      .step (.counter .borrow) (Function.update (other 0) track (digitTape bits 0)) .stay .stay .stay .stay none := by
    simp [TapeBank.instruction,bank,transition,configuration,head]
  apply TapeBank.RegionSteps.step _ (.counter .borrow) _ .stay .stay .stay .stay none 0 _
    (bounded track other data bits inputPosition radius .check valid) table
  have advanced : (bank I A O track).advance data (configuration track other bits inputPosition .check)
      (.counter .borrow) (Function.update (other 0) track (digitTape bits 0)) .stay .stay .stay .stay none=
      configuration track other bits inputPosition (.counter .borrow) := by
    simp [TapeBank.advance,configuration,bank,Move.onInt,Move.onInput,Nat.min_eq_left valid,Function.update_eq_self]
  rw [advanced]
  exact .refl _ (bounded track other data bits inputPosition radius (.counter .borrow) valid)

theorem left_step {I A O : Type} {tracks : ℕ} (track : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (data : InputData I A) (choices : BitString) (bits : List Bool) (inputPosition radius : ℕ)
    (valid : inputPosition+1≤data.input.length) :
    (bank I A O track).RegionSteps data choices radius (configuration track other bits (inputPosition+1) (.counter .done)) 1
      (configuration track other bits inputPosition .check) := by
  have table : (bank I A O track).instruction data (configuration track other bits (inputPosition+1) (.counter .done))=
      .step .check (Function.update (other 0) track (digitTape bits 0)) .stay .left .stay .stay none := rfl
  apply TapeBank.RegionSteps.step _ .check _ .stay .left .stay .stay none 0 _
    (bounded track other data bits (inputPosition+1) radius (.counter .done) valid) table
  have advanced : (bank I A O track).advance data (configuration track other bits (inputPosition+1) (.counter .done))
      .check (Function.update (other 0) track (digitTape bits 0)) .stay .left .stay .stay none=
      configuration track other bits inputPosition .check := by
    simp [TapeBank.advance,configuration,bank,Move.onInt,Move.onInput,Nat.min_eq_left (by omega : inputPosition≤data.input.length),
      Function.update_eq_self]
  rw [advanced]
  exact .refl _ (bounded track other data bits inputPosition radius .check (by omega))

theorem rewind_steps {I A O : Type} {tracks : ℕ} (track : Fin tracks) (other : ℤ→Fin tracks→Option Bool)
    (data : InputData I A) (choices : BitString) (count bound : ℕ)
    (size : count≤bound) (valid : count≤data.input.length) :
    ∃ time, (bank I A O track).RegionSteps data choices (2*Nat.clog 2 (bound+1)+4)
      (configuration track other (increment^[count] []) count .check) time
      (configuration track other [] 0 .check) := by
  induction count with
  | zero => exact ⟨0,.refl _ (bounded track other data [] 0 _ .check (Nat.zero_le _))⟩
  | succ count ih =>
      have nonempty : increment^[count+1] []≠[] := by
        rw [Function.iterate_succ_apply']
        exact increment_nonempty _
      have first := check_step (O:=O) track other data choices (increment^[count+1] []) nonempty
        (count+1) (2*Nat.clog 2 (bound+1)+4) valid
      obtain ⟨time,middle⟩ := decrement_steps (O:=O) track other data choices (increment^[count+1] [])
        (iterate_canonical _) bound (count+1) (by simpa only [iterate_value] using size) valid
      have digits : decrement (increment^[count+1] [])=increment^[count] [] := by
        rw [Function.iterate_succ_apply',decrement_increment _ (iterate_canonical count)]
      rw [digits] at middle
      have last := left_step (O:=O) track other data choices (increment^[count] []) count
        (2*Nat.clog 2 (bound+1)+4) valid
      obtain ⟨remaining,tail⟩ := ih (by omega) (by omega)
      exact ⟨1+time+1+remaining,
        ((first.trans (bank I A O track) middle).trans (bank I A O track) last).trans (bank I A O track) tail⟩

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.InputRewind
