import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
open BinaryCounter
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ}

/-- One call to the real decrement program, framed by arbitrary source work
and readonly positions, and returning the clock head to the origin. -/
theorem decrement_path (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (canonical : Canonical digits) (c : BankConfiguration O Q S k)
    (radius : ℕ) (bounded : source.Bounded data radius c) :
    ∃ time, time ≤ 2*digits.length+4 ∧
      (bank source).RegionSteps data choices (radius+2*digits.length+4)
        (configuration source digits c (.counter .borrow)) time
        (configuration source (decrement digits) c (.counter .done)) := by
  obtain ⟨time,budget,path⟩ := Decrement.decrement_steps (O:=O) data choices digits canonical
  have initial : (Decrement.bank I A O).Bounded data 0 (Decrement.encoded digits 0 .borrow) := by
    constructor <;> simp [Decrement.encoded]
  have localPath := (path.inRegion (Decrement.bank I A O) 0 initial).mono
    (Decrement.bank I A O) (show 0+time≤radius+2*digits.length+4 by omega)
  have framed := Context.regionSteps_frame (Decrement.bank I A O) (Decrement.workOnly I A O)
    data choices (context c) (context_valid source data radius c bounded) localPath
  let counterBank := BankEmbedding.bank (Decrement.bank I A O) k (fun bit => (source.blank,bit)) Prod.snd
  have lifted := BankEmbedding.regionSteps_lift (Decrement.bank I A O) (fun bit => (source.blank,bit)) Prod.snd
    (by intro bit;rfl) c.head (fun j position => (c.tape j position,none))
    (fun j => (bounded.head j).trans (by omega : radius≤radius+2*digits.length+4)) framed
  have mapped := lifted.mapState counterBank (bank source) (fun phase => (c.state,Phase.counter phase))
    (by intro phase;cases phase <;> rfl)
    (by
      intro phase input auxiliary index origin cell next write work i a x emit table
      cases phase with
      | done => simp [counterBank,BankEmbedding.bank,BankEmbedding.instruction,Decrement.bank,Decrement.transition] at table
      | borrow | inspect | erase | rewind => exact congrArg (BankInstruction.mapState (fun phase => (c.state,Phase.counter phase))) table)
    (by
      intro phase input auxiliary index origin cell no yes table
      cases phase <;> cases read : cell.2 with
      | none => simp [counterBank,BankEmbedding.bank,BankEmbedding.instruction,Decrement.bank,Decrement.transition,read] at table
      | some bit => cases bit <;> simp [counterBank,BankEmbedding.bank,BankEmbedding.instruction,Decrement.bank,Decrement.transition,read] at table)
  exact ⟨time,budget,by simpa only [counter_configuration] using mapped⟩

theorem check_path (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (nonempty : digits≠[]) (c : BankConfiguration O Q S k)
    (radius : ℕ) (bounded : source.Bounded data radius c) :
    (bank source).Steps data choices (configuration source digits c .check) 1
      (configuration source digits c (.counter .borrow)) := by
  apply (TapeBank.Steps.go (bank source) data choices _ (c.state,.counter .borrow)
    bounded.input bounded.auxiliary bounded.index ?_)
  cases digits with
  | nil => exact False.elim (nonempty rfl)
  | cons first rest =>
    simp [TapeBank.instruction,bank,configuration,transition,Fin.addCases_right,digitTape]

theorem continuation_path (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (c : BankConfiguration O Q S k)
    (radius : ℕ) (bounded : source.Bounded data radius c) :
    (bank source).Steps data choices (configuration source digits c (.counter .done)) 1
      (configuration source digits c .source) := by
  exact TapeBank.Steps.go (bank source) data choices _ (c.state,.source)
    bounded.input bounded.auxiliary bounded.index rfl

/-- The concrete check/decrement/continuation cycle has linear digit cost and
preserves every source tape and readonly head. -/
theorem cycle_path (source : TapeBank I A O Q S k) (data : InputData I A) (choices : BitString)
    (digits : List Bool) (canonical : Canonical digits) (nonempty : digits≠[])
    (c : BankConfiguration O Q S k) (radius : ℕ) (bounded : source.Bounded data radius c) :
    ∃ time, time≤2*digits.length+6 ∧
      (bank source).RegionSteps data choices (radius+2*digits.length+4)
        (configuration source digits c .check) time
        (configuration source (decrement digits) c .source) := by
  obtain ⟨time,budget,middle⟩ := decrement_path source data choices digits canonical c radius bounded
  have first := (check_path source data choices digits nonempty c radius bounded).inRegion (bank source)
    radius (configuration_bounded source data digits c .check radius bounded)
  have last := (continuation_path source data choices (decrement digits) c radius bounded).inRegion (bank source)
    radius (configuration_bounded source data (decrement digits) c (.counter .done) radius bounded)
  exact ⟨1+time+1,by omega,
    ((first.mono (bank source) (by omega)).trans (bank source) middle).trans
      (bank source) (last.mono (bank source) (by omega))⟩

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock
