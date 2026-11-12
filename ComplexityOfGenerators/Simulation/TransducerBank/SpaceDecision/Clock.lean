import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock.Semantics
import ComplexityOfGenerators.Simulation.TransducerBank.Uniqueness

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision

open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O QC SC QB SB : Type} {k m : ℕ}
  (constructor : TapeBank Unit Bool Unit QC SC k) (source : TapeBank I A O QB SB m)

theorem clock_executes_lift (copies length : ℕ) (digits : List Bool) (ctor : BankConfiguration Unit QC SC k)
    (data : InputData I A) (choices : BitString) (ticks : ℕ) (result : Outcome O)
    (run : (clockBank constructor source).Executes data choices
      (BinaryClock.configuration (sourceBank constructor source) digits (sourceConfiguration constructor source length ctor) .check) ticks result) :
    (bank constructor source copies).Executes data choices (clockConfiguration constructor source copies length digits ctor .check) ticks result := by
  have castRun := TapeCast.executes (clockBank constructor source) (tapeCount (m:=m) (k:=k)) run
  exact castRun.mapState (castClockBank constructor source) (bank constructor source copies) Sum.inr
    (by intro;rfl) (by intros;rfl)

theorem clock_regionRun_lift (copies length : ℕ) (digits : List Bool) (ctor : BankConfiguration Unit QC SC k)
    (data : InputData I A) (choices : BitString) (radius : ℕ) (result : Outcome O)
    (run : (clockBank constructor source).RegionRun data choices radius
      (BinaryClock.configuration (sourceBank constructor source) digits (sourceConfiguration constructor source length ctor) .check) result) :
    (bank constructor source copies).RegionRun data choices radius (clockConfiguration constructor source copies length digits ctor .check) result := by
  obtain ⟨ticks,finish,path,terminal⟩ := TapeCast.regionRun (clockBank constructor source) (tapeCount (m:=m) (k:=k)) run
  have mapped := path.mapState (castClockBank constructor source) (bank constructor source copies) Sum.inr
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work input auxiliary index emit table
      simpa only [bank,BankInstruction.mapState] using congrArg (BankInstruction.mapState Sum.inr) table)
    (by
      intro state i a x origin cell no yes table
      simpa only [bank,BankInstruction.mapState] using congrArg (BankInstruction.mapState Sum.inr) table)
  exact ⟨ticks,finish.mapState Sum.inr,mapped,
    terminal.mapState (castClockBank constructor source) (bank constructor source copies) Sum.inr (by intro;rfl) (by intros;rfl)⟩

theorem clock_execution (copies length : ℕ) (digits : List Bool) (canonical : Canonical digits)
    (ctor : BankConfiguration Unit QC SC k) (data : InputData I A) (choices : BitString) (radius : ℕ)
    (allBound : ∀ ticks finish,(sourceBank constructor source).Steps data choices (sourceConfiguration constructor source length ctor) ticks finish →
      (sourceBank constructor source).Bounded data radius finish) :
    ∃ ticks,ticks≤FixedBitBlocks.decode digits*(2*digits.length+8) ∧
      (bank constructor source copies).Executes data choices (clockConfiguration constructor source copies length digits ctor .check) ticks
        (BinaryClock.boundedResult (sourceBank constructor source) data choices (FixedBitBlocks.decode digits) (sourceConfiguration constructor source length ctor)) ∧
      (bank constructor source copies).RegionRun data choices (radius+2*digits.length+4)
        (clockConfiguration constructor source copies length digits ctor .check)
        (BinaryClock.boundedResult (sourceBank constructor source) data choices (FixedBitBlocks.decode digits) (sourceConfiguration constructor source length ctor)) := by
  obtain ⟨ticks,cost,run,region⟩ := BinaryClock.execution (sourceBank constructor source) data choices digits canonical
    (sourceConfiguration constructor source length ctor) radius allBound
  exact ⟨ticks,cost,clock_executes_lift constructor source copies length digits ctor data choices ticks _ run,
    clock_regionRun_lift constructor source copies length digits ctor data choices _ _ region⟩

theorem clock_accepted_iff (copies length : ℕ) (digits : List Bool) (canonical : Canonical digits)
    (ctor : BankConfiguration Unit QC SC k) (data : InputData I A) (choices : BitString) (radius : ℕ)
    (allBound : ∀ ticks finish,(sourceBank constructor source).Steps data choices (sourceConfiguration constructor source length ctor) ticks finish →
      (sourceBank constructor source).Bounded data radius finish) (word : List O) :
    (∃ ticks,(bank constructor source copies).Executes data choices (clockConfiguration constructor source copies length digits ctor .check) ticks (.accepted word)) ↔
      ∃ ticks,ticks<FixedBitBlocks.decode digits ∧
        (sourceBank constructor source).Executes data choices (sourceConfiguration constructor source length ctor) ticks (.accepted word) := by
  obtain ⟨ticks,cost,reference,region⟩ := clock_execution constructor source copies length digits canonical ctor data choices radius allBound
  constructor
  · rintro ⟨time,accepted⟩
    have same := TapeBank.Executes.result_unique (bank constructor source copies) reference accepted
    exact BinaryClock.boundedResult_accepts (sourceBank constructor source) data choices (FixedBitBlocks.decode digits)
      (sourceConfiguration constructor source length ctor) word same
  · rintro ⟨time,small,accepted⟩
    have same := BinaryClock.boundedResult_of_executes (sourceBank constructor source) accepted (FixedBitBlocks.decode digits) small
    exact ⟨ticks,by simpa only [same] using reference⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
