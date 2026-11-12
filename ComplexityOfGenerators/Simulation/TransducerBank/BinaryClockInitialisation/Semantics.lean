import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Seed
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Semantics

/-! A binary clock is materialised from an actual unary space constructor and
an actual binary count of the ordinary input length. The final clock/counter
contents and all head positions are explicit; neither is advice. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation

open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)

def width (copies n : ℕ) : ℕ := copies*(space n+Nat.clog 2 (n+1)+1)

def radius (copies n : ℕ) : ℕ :=
  constructor.constant*(space n+1)+(copies+20)*(space n+Nat.clog 2 (n+1)+1)

 theorem capture_region_supported (copies seed : ℕ) (data : InputData I A) (bits : BitString) :
    ∃ ticks ctor,
      (∀j,(ctor.head j).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      constructor.machine.program.TapeSupported (constructor.constant*(space data.input.length+1)) ctor ∧
      (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionSteps data bits
        (Capture.radius constructor copies seed data.input.length)
        (configuration constructor.machine.program copies (.capture (.construct constructor.machine.program.initial))
          (increment^[data.input.length] []) [] (List.replicate seed false) 0 0 seed constructor.machine.initialConfiguration)
        ticks
        (configuration constructor.machine.program copies (.capture .done) (increment^[data.input.length] []) []
          (List.replicate (seed+copies*space data.input.length) false++[true]) 0 0 0 ctor) := by
  obtain ⟨ticks,ctor,heads,supported,path⟩ := Capture.routine_regionSteps_supported (O:=O) constructor copies seed data bits
  have mapped := path.mapState (Capture.bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies)
    (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies) Phase.capture (by intro;rfl)
    (by
      intro q i a x origin cell next write work move aux index emit table
      simpa only [bank,BankInstruction.mapState] using congrArg (BankInstruction.mapState Phase.capture) table)
    (by
      intro q i a x origin cell no yes table
      simpa only [bank,BankInstruction.mapState] using congrArg (BankInstruction.mapState Phase.capture) table)
  exact ⟨ticks,ctor,heads,supported,by simpa only [←configuration_capture] using mapped⟩

 theorem capture_region (copies seed : ℕ) (data : InputData I A) (bits : BitString) :
    ∃ ticks ctor,
      (∀j,(ctor.head j).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionSteps data bits
        (Capture.radius constructor copies seed data.input.length)
        (configuration constructor.machine.program copies (.capture (.construct constructor.machine.program.initial))
          (increment^[data.input.length] []) [] (List.replicate seed false) 0 0 seed constructor.machine.initialConfiguration)
        ticks
        (configuration constructor.machine.program copies (.capture .done) (increment^[data.input.length] []) []
          (List.replicate (seed+copies*space data.input.length) false++[true]) 0 0 0 ctor) := by
  obtain ⟨ticks,ctor,heads,_,path⟩ := capture_region_supported (O:=O) constructor copies seed data bits
  exact ⟨ticks,ctor,heads,path⟩

/-- Starting from genuinely blank tapes, compute the input length, construct
and capture the space value, and reset the actual input and work heads. -/
theorem routine_regionSteps_supported (copies : ℕ) (data : InputData I A) (bits : BitString) :
    ∃ ticks ctor,
      (∀j,(ctor.head j).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      constructor.machine.program.TapeSupported (constructor.constant*(space data.input.length+1)) ctor ∧
      (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionSteps data bits
        (radius constructor copies data.input.length)
        (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).initialConfiguration ticks
        (configuration constructor.machine.program copies (.capture .done) (increment^[data.input.length] []) []
          (List.replicate (width (space:=space) copies data.input.length) false++[true]) 0 0 0 ctor) := by
  let n := data.input.length
  let logarithm := Nat.clog 2 (n+1)
  let total := radius constructor copies n
  have preludeRoom : 2*Nat.clog 2 (data.input.length+1)+4≤total := by
    dsimp [total,radius,n,logarithm]
    nlinarith
  obtain ⟨preludeTicks,preparation⟩ := prelude_region (O:=O) constructor.machine.program copies total data bits preludeRoom
  have freshHeads : ∀j,(constructor.machine.initialConfiguration.head j).natAbs≤total := by
    intro j;simp [MultitapeMachine.initialConfiguration,TapeBank.initialConfiguration]
  have toSeed := prelude_to_seed (O:=O) constructor.machine.program copies total data bits (increment^[data.input.length] [])
    constructor.machine.initialConfiguration freshHeads
  have seedRoom : (copies+5)*((increment^[data.input.length] []).length+1)≤total := by
    rw [iterate_length_eq]
    dsimp [total,radius,n,logarithm]
    nlinarith
  have seeding := seed_region (O:=O) constructor.machine.program copies total data bits (increment^[data.input.length] [])
    constructor.machine.initialConfiguration freshHeads seedRoom
  have toCapture := seed_to_capture (O:=O) constructor.machine.program copies total data bits (increment^[data.input.length] [])
    constructor.machine.initialConfiguration freshHeads (by nlinarith)
  let seed := copies*((increment^[data.input.length] []).length+1)
  obtain ⟨captureTicks,ctor,heads,supported,capturing⟩ := capture_region_supported (O:=O) constructor copies seed data bits
  have captureRoom : Capture.radius constructor copies seed data.input.length≤total := by
    dsimp [Capture.radius,seed]
    rw [iterate_length_eq]
    dsimp [total,radius,n,logarithm]
    nlinarith
  have width_eq : seed+copies*space data.input.length=width (space:=space) copies data.input.length := by
    dsimp [seed,width]
    rw [iterate_length_eq]
    ring
  rw [width_eq] at capturing
  refine ⟨preludeTicks+1+(copies+1+((copies+3)*(increment^[data.input.length] []).length+1)+
    ((increment^[data.input.length] []).length+1))+1+captureTicks,ctor,heads,supported,?_⟩
  exact (((preparation.trans _ toSeed).trans _ seeding).trans _ toCapture).trans _ (capturing.mono _ captureRoom)

theorem routine_regionSteps (copies : ℕ) (data : InputData I A) (bits : BitString) :
    ∃ ticks ctor,
      (∀j,(ctor.head j).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionSteps data bits
        (radius constructor copies data.input.length)
        (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).initialConfiguration ticks
        (configuration constructor.machine.program copies (.capture .done) (increment^[data.input.length] []) []
          (List.replicate (width (space:=space) copies data.input.length) false++[true]) 0 0 0 ctor) := by
  obtain ⟨ticks,ctor,heads,_,path⟩ := routine_regionSteps_supported (O:=O) constructor copies data bits
  exact ⟨ticks,ctor,heads,path⟩

/-- The clock handoff is reached on every finite choice tape, with output and
choice head unchanged. The bound depends on space, never constructor time. -/
theorem routine_region (copies : ℕ) (data : InputData I A) (bits : BitString) :
    (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionRun data bits
      (radius constructor copies data.input.length)
      (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).initialConfiguration (.accepted []) := by
  obtain ⟨ticks,ctor,heads,path⟩ := routine_regionSteps (O:=O) constructor copies data bits
  exact ⟨ticks,_,path,.accept _ rfl⟩

 theorem spaceBound (copies : ℕ) (data : InputData I A) :
    (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).SpaceBound data
      (radius constructor copies data.input.length) := by
  apply TapeBank.spaceBound_of_regionRuns
  intro bits
  exact ⟨.accepted [],routine_region constructor copies data bits⟩

 theorem radius_le (copies n : ℕ) :
    radius constructor copies n ≤ (constructor.constant+copies+20)*(space n+Nat.clog 2 (n+1)+1) := by
  unfold radius
  nlinarith

end
end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation
