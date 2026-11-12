import ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision.Basic
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClockInitialisation.Semantics
import ComplexityOfGenerators.Simulation.TransducerBank.FixedChoice
import ComplexityOfGenerators.Simulation.TransducerBank.BinaryClock.Semantics

namespace ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision

open BinaryCounter
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O QC SC QB SB : Type} {k m : ℕ}

theorem initial_lift (constructor : TapeBank Unit Bool Unit QC SC k) (source : TapeBank I A O QB SB m) (copies : ℕ) :
    (BankEmbedding.lift (encodeInitial source.blank) (fun _ : Fin m => 0)
      (fun _ _ => ((constructor.blank,((fun _ => none),source.blank)),none))
      (BinaryClockInitialisation.bank (I:=I) (A:=A) (O:=O) constructor copies).initialConfiguration).mapState Sum.inl=
      (bank constructor source copies).initialConfiguration := by
  apply BankConfiguration.ext <;> try rfl
  · funext index
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;>
      simp [BankEmbedding.lift,BankConfiguration.mapState,TapeBank.initialConfiguration,bank,initialBank]
  · funext index position
    refine Fin.addCases (fun index => ?_) (fun index => ?_) index <;>
      simp [BankEmbedding.lift,BankConfiguration.mapState,TapeBank.initialConfiguration,bank,initialBank,
        BinaryClockInitialisation.bank,encodeInitial,BankEmbedding.bank]

/-- One fixed actual initializer path works on every choice tape. Its empty
consumed random interval preserves the exact dirty constructor snapshot. -/
theorem initialized_steps {space : ℕ→ℕ} (constructor : Multitape.SpaceConstructor space)
    (source : TapeBank I A O QB SB m) (copies : ℕ) (data : InputData I A) :
    ∃ ticks ctor,
      (∀ tape,(ctor.head tape).natAbs≤constructor.constant*(space data.input.length+1)) ∧
      constructor.machine.program.TapeSupported (constructor.constant*(space data.input.length+1)) ctor ∧
      ∀ choices,(bank constructor.machine.program source copies).RegionSteps data choices
        (BinaryClockInitialisation.radius constructor copies data.input.length)
        (bank constructor.machine.program source copies).initialConfiguration ticks
        (initialConfiguration constructor.machine.program source copies data.input.length
          (BinaryClock.powerDigits (BinaryClockInitialisation.width (space:=space) copies data.input.length)) ctor) := by
  obtain ⟨ticks,ctor,heads,support,path⟩ := BinaryClockInitialisation.routine_regionSteps_supported (O:=O) constructor copies data []
  refine ⟨ticks,ctor,heads,support,?_⟩
  intro choices
  have replay := path.change_bits_interval
    (BinaryClockInitialisation.bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies) choices (by
      intro index lower upper
      change index<0 at upper
      omega)
  have lifted := BankEmbedding.regionSteps_lift
    (BinaryClockInitialisation.bank (I:=I) (A:=A) (O:=O) constructor.machine.program copies)
    (encodeInitial source.blank) decodeInitial (by intro;rfl) (fun _ : Fin m => 0)
    (fun _ _ => ((constructor.machine.program.blank,((fun _ => none),source.blank)),none))
    (by intro;simp) replay
  have mapped := lifted.mapState (initialBank constructor.machine.program source copies)
    (bank constructor.machine.program source copies) Sum.inl
    (by intro;rfl)
    (by
      intro state i a x origin cell next write work move aux index emit table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Sum.inl (Sum.inr (source.initial,BinaryClock.Phase.check)) cell) table)
    (by
      intro state i a x origin cell no yes table
      simpa only [bank,Prelude.continueInstruction] using
        congrArg (Prelude.continueInstruction Sum.inl (Sum.inr (source.initial,BinaryClock.Phase.check)) cell) table)
  rw [initial_lift] at mapped
  exact mapped

end
end ComplexityOfGenerators.Simulation.TransducerBank.SpaceDecision
