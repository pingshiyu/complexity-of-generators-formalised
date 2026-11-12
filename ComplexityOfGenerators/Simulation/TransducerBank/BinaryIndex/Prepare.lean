import ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex.SourceStep
import ComplexityOfGenerators.Simulation.TransducerBank.RegionEmbedding

namespace ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
open BinaryCounter
set_option backward.isDefEq.respectTransparency false
variable {I A O Q S : Type} {k : ℕ} (source : TapeBank I A O Q S k)

theorem counterMemory_zero (length : ℕ) (position : ℤ) :
    counterMemory length 0 position=Prelude.memory (increment^[length] []) [] position := by
  rw [Prelude.memory_empty_temporary]
  funext track
  by_cases first : track=0
  · subst track
    simp [counterMemory]
  · by_cases second : track=1
    · subst track
      simp [counterMemory,digitTape]
    · simp [counterMemory,Function.update_of_ne first,Function.update_of_ne second]

theorem prepare_lift_initial :
    (LeftBankEmbedding.lift (encodeCounter source) (fun _ : Fin k => 0)
      (fun _ _ => encodeSource source.blank) (Prelude.bank I A O).initialConfiguration).mapState Control.prepare =
      (bank source).initialConfiguration := by
  apply BankConfiguration.ext <;> try rfl
  · funext j
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [LeftBankEmbedding.lift,BankConfiguration.mapState,TapeBank.initialConfiguration,Prelude.bank,bank]
  · funext j position
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j <;>
      simp [LeftBankEmbedding.lift,BankConfiguration.mapState,TapeBank.initialConfiguration,Prelude.bank,bank,encodeCounter,encodeSource]

theorem prepare_lift_final (length : ℕ) :
    (LeftBankEmbedding.lift (encodeCounter source) (fun _ : Fin k => 0)
      (fun _ _ => encodeSource source.blank) (Prelude.configuration (increment^[length] []) [] 0 Prelude.Control.done)).mapState Control.prepare =
      configuration source length 0 source.initialConfiguration (.prepare .done) := by
  apply BankConfiguration.ext <;> try rfl
  funext j position
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · simp only [LeftBankEmbedding.lift,BankConfiguration.mapState,Prelude.configuration,configuration,
      Fin.addCases_left,counterMemory_zero]
  · simp [LeftBankEmbedding.lift,BankConfiguration.mapState,Prelude.configuration,configuration,TapeBank.initialConfiguration]

/-- Actual unary-input counting, binary counter setup, and input rewind.
The source bank stays blank and every head is returned to its origin. -/
theorem prepare_steps (data : InputData I A) (choices : BitString) :
    ∃ time, (bank source).RegionSteps data choices (2*Nat.clog 2 (data.input.length+1)+4)
      (bank source).initialConfiguration time
      (configuration source data.input.length 0 source.initialConfiguration (.probe source.initial (.scan false))) := by
  obtain ⟨time,path⟩ := Prelude.prepared_steps (O:=O) data choices
  have lifted := LeftBankEmbedding.regionSteps_lift (Prelude.bank I A O) (encodeCounter source) Prod.snd
    (by intro cell;rfl) (fun _ : Fin k => 0) (fun _ _ => encodeSource source.blank) (by intro;simp) path
  have mapped := lifted.mapState (prepareBank source) (bank source) Control.prepare
    (by intro state;rfl)
    (by
      intro state input auxiliary index origin cell next write work i a x emit table
      simpa only [bank,transition,Prelude.continueInstruction] using congrArg
        (Prelude.continueInstruction Control.prepare (.probe source.initial (.scan false)) cell) table)
    (by
      intro state input auxiliary index origin cell no yes table
      simpa only [bank,transition,Prelude.continueInstruction] using congrArg
        (Prelude.continueInstruction Control.prepare (.probe source.initial (.scan false)) cell) table)
  rw [prepare_lift_initial,prepare_lift_final] at mapped
  have sourceBound := source.initial_bounded (sourceData data)
  have bounded := configuration_bounded source data data.input.length 0 source.initialConfiguration (.prepare .done) 0 sourceBound
  have handoff : (bank source).Steps data choices
      (configuration source data.input.length 0 source.initialConfiguration (.prepare .done)) 1
      (configuration source data.input.length 0 source.initialConfiguration (.probe source.initial (.scan false))) :=
    TapeBank.Steps.go (bank source) data choices _ (.probe source.initial (.scan false))
      bounded.input bounded.auxiliary bounded.index rfl
  exact ⟨time+1,mapped.trans (bank source) ((handoff.inRegion (bank source) 0 bounded).mono (bank source) (by omega))⟩

end ComplexityOfGenerators.Simulation.TransducerBank.BinaryIndex
