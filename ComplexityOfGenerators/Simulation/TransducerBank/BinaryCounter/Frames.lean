import ComplexityOfGenerators.Simulation.TransducerBank.PassiveContext
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Decrement
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryCounter.Copy
import ComplexityOfGenerators.Simulation.TransducerBank.Tracks

namespace ComplexityOfGenerators.Simulation.TransducerBank

set_option backward.isDefEq.respectTransparency false

theorem Tracks.workOnly {I A O Q S : Type} {k tracks : ℕ} (source : TapeBank I A O Q S k)
    (track : Fin tracks) (passive : source.WorkOnly) : (Tracks.bank source track).WorkOnly := by
  constructor
  · intro state input auxiliary index origin cell
    simp only [Tracks.bank]
    rw [passive.independent]
  · intro state input auxiliary index origin cell
    have silent := passive.silent state input auxiliary index origin (cell track)
    cases table : source.transition state input auxiliary index origin (cell track) with
    | accept => simp [Tracks.bank,Tracks.instruction,table]
    | reject => simp [Tracks.bank,Tracks.instruction,table]
    | readRandom no yes => simp [table] at silent
    | step next write work i a x emit =>
        rw [table] at silent
        obtain ⟨rfl,rfl,rfl,rfl⟩ := silent
        simp [Tracks.bank,Tracks.instruction,table]

namespace BinaryCounter

theorem increment_workOnly (I A O : Type) : (bank I A O).WorkOnly := by
  constructor
  · intros; rfl
  · intro phase input auxiliary index origin cell
    cases phase <;> by_cases good : cell=some true <;> simp [bank,transition,good]

theorem Decrement.workOnly (I A O : Type) : (Decrement.bank I A O).WorkOnly := by
  constructor
  · intros; rfl
  · intro state input auxiliary index origin cell
    cases state <;> cases cell with
    | none => simp [Decrement.bank,Decrement.transition]
    | some bit => cases bit <;> simp [Decrement.bank,Decrement.transition]

theorem Copy.workOnly (I A O : Type) {tracks : ℕ} (fromTrack target : Fin tracks) :
    (Copy.bank I A O fromTrack target).WorkOnly := by
  constructor
  · intros; rfl
  · intro state input auxiliary index origin cell
    cases state with
    | done => trivial
    | rewind => simp [Copy.bank,Copy.transition]
    | copy =>
        cases read : cell fromTrack <;> simp [Copy.bank,Copy.transition,read]

theorem decrement_framed {I A O : Type} (data : InputData I A) (choices : BitString)
    (context : Context O) (valid : context.Valid data) (bits : List Bool) (canonical : Canonical bits)
    (bound : ℕ) (value : FixedBitBlocks.decode bits≤bound) :
    ∃ time, (Decrement.bank I A O).RegionSteps data choices (2*Nat.clog 2 (bound+1)+4)
      (context.frame (Decrement.encoded bits 0 .borrow)) time (context.frame (Decrement.encoded (decrement bits) 0 .done)) := by
  obtain ⟨time,path⟩ := Decrement.decrement_regionSteps (O:=O) data choices bits canonical bound value
  exact ⟨time,Context.regionSteps_frame (Decrement.bank I A O) (Decrement.workOnly I A O)
    data choices context valid path⟩

theorem copy_framed {I A O : Type} {tracks : ℕ} (fromTrack target : Fin tracks) (different : fromTrack≠target)
    (other : ℤ→Fin tracks→Option Bool) (data : InputData I A) (choices : BitString)
    (context : Context O) (valid : context.Valid data) (bits : List Bool) (canonical : Canonical bits)
    (bound : ℕ) (value : FixedBitBlocks.decode bits≤bound) :
    (Copy.bank I A O fromTrack target).RegionSteps data choices (2*Nat.clog 2 (bound+1)+2)
      (context.frame (Copy.encoded fromTrack target other bits [] 0 .copy)) (2*(bits.length+1))
      (context.frame (Copy.encoded fromTrack target other bits bits 0 .done)) := by
  exact Context.regionSteps_frame (Copy.bank I A O fromTrack target) (Copy.workOnly I A O fromTrack target)
    data choices context valid (Copy.routine_regionSteps fromTrack target different other data choices bits canonical bound value)

end BinaryCounter
end ComplexityOfGenerators.Simulation.TransducerBank
