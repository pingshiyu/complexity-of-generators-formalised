import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Initialisation
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Handoff
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Source
import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Clock

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision

open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O QB SB : Type} {m : ℕ}

theorem prepared_steps {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)
    (source : TapeBank I A O QB SB m) (copies : ℕ) (data : InputData I A) :
    ∃ ticks ctor,
      (∀ tape,(ctor.head tape).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      constructor.machine.program.TapeSupported (constructor.constant*(space data.input.length+1)) ctor ∧
      ∀ choices,(bank constructor.machine.program source copies).RegionSteps data choices
        (BinaryClockInitialisation.radius constructor copies data.input.length)
        (bank constructor.machine.program source copies).initialConfiguration ticks
        (clockConfiguration constructor.machine.program source copies data.input.length
          (BinaryClock.powerDigits (BinaryClockInitialisation.width (space:=space) copies data.input.length)) ctor .check) := by
  obtain ⟨ticks,ctor,heads,support,path⟩ := initialized_steps constructor source copies data
  refine ⟨ticks+1,ctor,heads,support,?_⟩
  intro choices
  exact (path choices).trans _ (handoff_path constructor.machine.program source copies data.input.length _ ctor data choices
    _ ((path choices).end_bound _))

theorem prefix_accepted_iff {QC SC : Type} {k : ℕ} (constructor : TapeBank Unit Bool Unit QC SC k)
    (source : TapeBank I A O QB SB m) (copies length : ℕ) (digits : List Bool) (canonical : Canonical digits)
    (ctor : BankConfiguration Unit QC SC k) (data : InputData I A) (choices : BitString) (radius prefixTicks : ℕ)
    (allBound : ∀ ticks finish,(sourceBank constructor source).Steps data choices (sourceConfiguration constructor source length ctor) ticks finish →
      (sourceBank constructor source).Bounded data radius finish)
    (preparation : (bank constructor source copies).Steps data choices (bank constructor source copies).initialConfiguration prefixTicks
      (clockConfiguration constructor source copies length digits ctor .check)) (word : List O) :
    (∃ ticks,(bank constructor source copies).Executes data choices (bank constructor source copies).initialConfiguration ticks (.accepted word)) ↔
      ∃ ticks,ticks<FixedBitBlocks.decode digits ∧
        (sourceBank constructor source).Executes data choices (sourceConfiguration constructor source length ctor) ticks (.accepted word) := by
  obtain ⟨ticks,cost,reference,region⟩ := clock_execution constructor source copies length digits canonical ctor data choices radius allBound
  constructor
  · rintro ⟨time,accepted⟩
    have whole := preparation.executes _ reference
    have same := TapeBank.Executes.result_unique (bank constructor source copies) whole accepted
    apply (clock_accepted_iff constructor source copies length digits canonical ctor data choices radius allBound word).mp
    exact ⟨ticks,by simpa only [same] using reference⟩
  · intro short
    obtain ⟨time,accepted⟩ := (clock_accepted_iff constructor source copies length digits canonical ctor data choices radius allBound word).mpr short
    exact ⟨prefixTicks+time,preparation.executes _ accepted⟩

def sourceRadius {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space) (base n : ℕ) :=
  base+constructor.constant*(space n+1)+Nat.clog 2 (n+1)+1

def totalRadius {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space) (copies base n : ℕ) :=
  max (BinaryClockInitialisation.radius constructor copies n)
    (sourceRadius constructor base n+2*(BinaryClockInitialisation.width (space:=space) copies n+1)+4)

/-- The complete native decision controller has one common finite deadline
on all random tapes. Constructor time may be unbounded as a function of the
space resource; its actual finite preparation is charged once before the clock. -/
theorem execution {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)
    (source : TapeBank I A O QB SB m) (copies : ℕ) (data : InputData I A) (base : ℕ)
    (bounded : source.SpaceBound data base)
    (termination : ∀ choices,∃ ticks result,source.Executes data choices source.initialConfiguration ticks result) :
    ∃ prefixTicks ctor,
      (∀ tape,(ctor.head tape).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      constructor.machine.program.TapeSupported (constructor.constant*(space data.input.length+1)) ctor ∧
      ∀ choices,∃ ticks result,
        ticks≤prefixTicks+2^(BinaryClockInitialisation.width (space:=space) copies data.input.length)*
          (2*(BinaryClockInitialisation.width (space:=space) copies data.input.length+1)+8) ∧
        (bank constructor.machine.program source copies).Executes data choices (bank constructor.machine.program source copies).initialConfiguration ticks result ∧
        (bank constructor.machine.program source copies).RegionRun data choices (totalRadius constructor copies base data.input.length)
          (bank constructor.machine.program source copies).initialConfiguration result := by
  obtain ⟨prefixTicks,ctor,heads,support,preparation⟩ := prepared_steps constructor source copies data
  refine ⟨prefixTicks,ctor,heads,support,?_⟩
  intro choices
  let digits := BinaryClock.powerDigits (BinaryClockInitialisation.width (space:=space) copies data.input.length)
  let radius := sourceRadius constructor base data.input.length
  have baseRoom : base≤radius := by dsimp [radius,sourceRadius];omega
  have ctorRoom : constructor.constant*(space data.input.length+1)≤radius := by dsimp [radius,sourceRadius];omega
  have heads' : ∀ tape,(ctor.head tape).natAbs≤radius := fun tape => (heads tape).trans ctorRoom
  have space' : source.SpaceBound data radius := fun bits ticks finish path => (bounded bits ticks finish path).mono source baseRoom
  have allBound := source_future_bound constructor.machine.program source data data.input.length radius ctor heads' space' termination choices
  obtain ⟨clockTicks,cost,clockRun,clockRegion⟩ := clock_execution constructor.machine.program source copies data.input.length digits
    (BinaryClock.powerDigits_canonical _) ctor data choices radius allBound
  let result := BinaryClock.boundedResult (sourceBank constructor.machine.program source) data choices (FixedBitBlocks.decode digits)
    (sourceConfiguration constructor.machine.program source data.input.length ctor)
  have whole : (bank constructor.machine.program source copies).Executes data choices
      (bank constructor.machine.program source copies).initialConfiguration (prefixTicks+clockTicks) result :=
    ((preparation choices).toSteps _).executes _ clockRun
  have clockRoom : radius+2*digits.length+4≤totalRadius constructor copies base data.input.length := by
    simp only [digits,BinaryClock.powerDigits_length,radius,totalRadius]
    exact Nat.le_max_right _ _
  have wholeRegion : (bank constructor.machine.program source copies).RegionRun data choices
      (totalRadius constructor copies base data.input.length) (bank constructor.machine.program source copies).initialConfiguration result :=
    (clockRegion.mono _ clockRoom).prepend _ ((preparation choices).mono _ (Nat.le_max_left _ _))
  refine ⟨prefixTicks+clockTicks,result,?_,whole,wholeRegion⟩
  have deadline : clockTicks≤2^(BinaryClockInitialisation.width (space:=space) copies data.input.length)*
      (2*(BinaryClockInitialisation.width (space:=space) copies data.input.length+1)+8) := by
    simpa only [digits,BinaryClock.powerDigits_value,BinaryClock.powerDigits_length] using cost
  exact Nat.add_le_add_left deadline _

theorem bounded_termination {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)
    (source : TapeBank I A O QB SB m) (copies : ℕ) (data : InputData I A) (base : ℕ)
    (bounded : source.SpaceBound data base)
    (termination : ∀ choices,∃ ticks result,source.Executes data choices source.initialConfiguration ticks result) :
    ∃ deadline,∀ choices,∃ ticks result,ticks≤deadline ∧
      (bank constructor.machine.program source copies).Executes data choices (bank constructor.machine.program source copies).initialConfiguration ticks result := by
  obtain ⟨prefixTicks,ctor,heads,support,all⟩ := execution constructor source copies data base bounded termination
  exact ⟨prefixTicks+2^(BinaryClockInitialisation.width (space:=space) copies data.input.length)*
      (2*(BinaryClockInitialisation.width (space:=space) copies data.input.length+1)+8),
    fun choices => by obtain ⟨ticks,result,cost,run,region⟩ := all choices;exact ⟨ticks,result,cost,run⟩⟩

theorem spaceBound {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)
    (source : TapeBank I A O QB SB m) (copies : ℕ) (data : InputData I A) (base : ℕ)
    (bounded : source.SpaceBound data base)
    (termination : ∀ choices,∃ ticks result,source.Executes data choices source.initialConfiguration ticks result) :
    (bank constructor.machine.program source copies).SpaceBound data (totalRadius constructor copies base data.input.length) := by
  obtain ⟨prefixTicks,ctor,heads,support,all⟩ := execution constructor source copies data base bounded termination
  apply TapeBank.spaceBound_of_regionRuns
  intro choices
  obtain ⟨ticks,result,cost,run,region⟩ := all choices
  exact ⟨result,region⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
