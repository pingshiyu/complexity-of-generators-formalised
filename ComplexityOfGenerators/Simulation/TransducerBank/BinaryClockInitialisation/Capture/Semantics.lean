import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Finish
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture.Reset
import ComplexityOfGenerators.Simulation.TransducerBank.RegionTapeSupport

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture

open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O : Type} {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)

def radius (copies seed n : ℕ) : ℕ :=
  constructor.constant*(space n+1)+seed+copies*space n+3+(2*Nat.clog 2 (n+1)+4)

/-- A real unary space computation appends the requested clock digits and
returns all readonly, counter and clock heads to their initial positions.
Its dirty work tapes are retained in the handoff configuration. -/
theorem routine_regionSteps_supported (copies seed : ℕ) (data : InputData I A) (bits : BitString) :
    ∃ ticks ctor,
      (∀j,(ctor.head j).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      constructor.machine.program.TapeSupported (constructor.constant*(space data.input.length+1)) ctor ∧
      (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionSteps data bits
        (radius constructor copies seed data.input.length)
        (configuration constructor.machine.program copies (.construct constructor.machine.program.initial)
          (increment^[data.input.length] []) [] (List.replicate seed false) 0 0 seed constructor.machine.initialConfiguration)
        ticks
        (configuration constructor.machine.program copies .done (increment^[data.input.length] []) []
          (List.replicate (seed+copies*space data.input.length) false++[true]) 0 0 0 ctor) := by
  obtain ⟨ctorTicks,ctor,path,halt⟩ := constructor.computes data.input.length
  have terminal : constructor.machine.program.instruction (decisionData (List.replicate data.input.length ())) ctor=.accept ∧
      ctor.output=List.replicate (space data.input.length) () := by
    generalize outcome : Outcome.accepted (List.replicate (space data.input.length) ())=result at halt
    cases halt with
    | accept ctor table => exact ⟨table,(Outcome.accepted.inj outcome).symm⟩
    | reject => cases outcome
    | exhausted => cases outcome
  obtain ⟨table,output⟩ := terminal
  obtain ⟨actual,simulation⟩ := constructor_region (O:=O) constructor.machine.program copies seed (space data.input.length)
    (constructor.constant*(space data.input.length+1)) data bits (increment^[data.input.length] []) []
    constructor.deterministic path (by simp [output])
  have ctorBound := path.end_bound constructor.machine.program
  have within : ctor.inputHead≤data.input.length := by simpa [decisionData] using ctorBound.input
  have finish := finish_region (O:=O) constructor.machine.program copies
    (constructor.constant*(space data.input.length+1)+seed+copies*space data.input.length+3)
    (seed+copies*space data.input.length) data bits (increment^[data.input.length] []) [] ctor within
    (fun j=>(ctorBound.head j).trans (by omega)) (by omega) table
  have simulation' : (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionSteps data bits
      (constructor.constant*(space data.input.length+1)+seed+copies*space data.input.length+3)
      (configuration constructor.machine.program copies (.construct constructor.machine.program.initial)
        (increment^[data.input.length] []) [] (List.replicate seed false) 0 0 seed constructor.machine.initialConfiguration)
      actual
      (configuration constructor.machine.program copies (.construct ctor.state)
        (increment^[data.input.length] []) [] (List.replicate (seed+copies*space data.input.length) false)
        ctor.inputHead 0 (seed+copies*space data.input.length) ctor) := by
    simpa [TapeBank.initialConfiguration,output,Nat.cast_add,Nat.cast_mul] using simulation
  have reset := reset_regionSteps (O:=O) constructor.machine.program copies
    (constructor.constant*(space data.input.length+1)) data bits
    (List.replicate (seed+copies*space data.input.length) false++[true]) ctor.inputHead ctor within ctorBound.head
  obtain ⟨resetTicks,resetPath⟩ := reset
  have prefixPath := simulation'.trans (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies) finish
  refine ⟨actual+(2+(seed+copies*space data.input.length+1))+resetTicks,ctor,ctorBound.head,path.tapeSupported constructor.machine.program (constructor.machine.program.initial_tapeSupported _),?_⟩
  exact (prefixPath.mono _ (by unfold radius;omega)).trans _ (resetPath.mono _ (by unfold radius;omega))

/-- The original handoff API, without the additional snapshot-support fact. -/
theorem routine_regionSteps (copies seed : ℕ) (data : InputData I A) (bits : BitString) :
    ∃ ticks ctor,
      (∀j,(ctor.head j).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      (bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies).RegionSteps data bits
        (radius constructor copies seed data.input.length)
        (configuration constructor.machine.program copies (.construct constructor.machine.program.initial)
          (increment^[data.input.length] []) [] (List.replicate seed false) 0 0 seed constructor.machine.initialConfiguration)
        ticks
        (configuration constructor.machine.program copies .done (increment^[data.input.length] []) []
          (List.replicate (seed+copies*space data.input.length) false++[true]) 0 0 0 ctor) := by
  obtain ⟨ticks,ctor,heads,_,path⟩ := routine_regionSteps_supported (O:=O) constructor copies seed data bits
  exact ⟨ticks,ctor,heads,path⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Capture
