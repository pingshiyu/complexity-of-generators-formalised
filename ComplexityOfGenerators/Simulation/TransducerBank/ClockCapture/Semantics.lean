import ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture.Execution
import ComplexityOfGenerators.MultitapeConstructibility

/-! The clock is constructed and captured by a finite program, then consumed
by the finite source controller. Every finite choice tape terminates in O(t),
even when an unclocked source has divergent or long unsuccessful branches. -/

namespace ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {O : Type} {time : ℕ→ℕ}
  (constructor : Multitape.TimeConstructor time) (source : MultitapeMachine Unit Bool O)

def machine (copies : ℕ) : MultitapeMachine Unit Bool O := by
  letI : Finite O := source.outputFinite
  letI : Fintype O := Fintype.ofFinite O
  exact
    { inputFinite := inferInstance
      auxiliaryFinite := inferInstance
      outputFinite := source.outputFinite
      Control := Control (QC:=constructor.machine.Control) (Q:=source.Control)
        (S:=source.Work) (O:=O) (k:=source.tapes) copies
      Work := Cell (SC:=constructor.machine.Work) (S:=source.Work)
      controlFinite := inferInstance
      workFinite := inferInstance
      tapes := constructor.machine.tapes+(source.tapes+1)
      program := bank constructor.machine.program source.program copies }

def runtime (copies : ℕ) (n : ℕ) : ℕ :=
  ((copies+2)*constructor.constant+5*copies+10)*(time n+1)

 theorem timeBound (copies : ℕ) (positive : 1≤copies) (dominates : ∀ n,n≤time n) (n : ℕ) :
    (machine constructor source copies).TimeBound (generatorData n) (runtime constructor copies n) := by
  intro bits
  obtain ⟨ctorTicks,ctorCost,ctorRun⟩ := constructor.computes n
  obtain ⟨ticks,result,cost,execution,_⟩ := bounded_execution constructor.machine.program source.program
    copies n (time n) ctorTicks positive (dominates n) constructor.deterministic ctorRun bits
  refine ⟨ticks,result,?_,execution⟩
  have scaled := Nat.mul_le_mul_left (copies+2) ctorCost
  unfold runtime
  nlinarith

 theorem produces_iff (copies : ℕ) (positive : 1≤copies) (dominates : ∀ n,n≤time n)
    (n : ℕ) (bits : BitString) (word : Word O) :
    (machine constructor source copies).Produces (generatorData n) bits word ↔
      ∃ ticks,ticks≤copies*(time n+1) ∧
        source.Executes (generatorData n) bits source.initialConfiguration ticks (.accepted word) := by
  obtain ⟨ticks,_,run⟩ := constructor.computes n
  exact accepted_iff constructor.machine.program source.program copies n (time n) ticks positive
    (dominates n) constructor.deterministic run bits word

 theorem terminates (copies : ℕ) (positive : 1≤copies) (dominates : ∀ n,n≤time n) (n : ℕ) :
    (machine constructor source copies).Terminates (generatorData n) := by
  intro bits
  obtain ⟨ticks,result,_,run⟩ := timeBound constructor source copies positive dominates n bits
  exact ⟨ticks,result,run⟩

 theorem produces_iff_of_accepting_bound (copies : ℕ) (positive : 1≤copies) (dominates : ∀ n,n≤time n)
    (bounded : ∀ n,source.AcceptingTimeBound (generatorData n) (copies*(time n+1)))
    (n : ℕ) (bits : BitString) (word : Word O) :
    (machine constructor source copies).Produces (generatorData n) bits word ↔
      source.Produces (generatorData n) bits word := by
  rw [produces_iff constructor source copies positive dominates]
  constructor
  · rintro ⟨ticks,_,run⟩
    exact ⟨ticks,run⟩
  · rintro ⟨ticks,run⟩
    exact ⟨ticks,bounded n bits ticks word run,run⟩

 theorem resourceOrder (copies : ℕ) (dominates : ∀ n,n≤time n) :
    Multitape.ResourceOrder (runtime constructor copies) time := by
  let coefficient := (copies+2)*constructor.constant+5*copies+10
  refine ⟨2*coefficient,1,by dsimp [coefficient]; omega,?_⟩
  intro n large
  have positive : 1≤time n := large.trans (dominates n)
  change coefficient*(time n+1)≤(2*coefficient)*time n
  calc
    coefficient*(time n+1) ≤ coefficient*(2*time n) := Nat.mul_le_mul_left _ (by omega)
    _ = (2*coefficient)*time n := by ac_rfl

end
end ComplexityOfGenerators.Simulation.TransducerBank.ClockCapture
