import ComplexityOfGenerators.Simulation.SavitchMachine.AlphabetSearch

/-! A concrete base subprogram for constant graph predicates. This also
provides an executable instance of the complete recursive control table,
including successful and unsuccessful midpoint searches. -/

namespace ComplexityOfGenerators.Simulation.SavitchMachine.AlphabetSearch

open Turing StackSpace Complexity Frames
set_option backward.isDefEq.respectTransparency false

def constantBase {α : Type} (result : Bool) (_ : Unit) : Code α Unit :=
  .load (fun v => ({v.1 with returned := some result}, none)) (.goto fun _ => loadPhase 0)

theorem constantBase_correct {α : Type} (result : Bool) (input : List α) (r : ℕ)
    (room : input.length ≤ r) :
    BaseCorrect () (constantBase result) input (fun _ _ => result) (fun _ => result) r := by
  intro a f fs _ bound
  have popped := pop_frame (SavitchMachine.program () (fun _ => .halt)) erasePhase loadPhase
    (program_load () (fun _ => .halt)) (program_erase () (fun _ => .halt)) rfl
    (status ⟨false, a, some result, f :: fs⟩) f fs r bound
  change Trace _ r (SavitchMachine.encoded (loadPhase 0) ⟨false, a, some result, f :: fs⟩)
    (SavitchMachine.encoded .dispatch ⟨false, a, some result, fs⟩) at popped
  have tail := lift_trace () (constantBase result) popped
    (by simp [SavitchMachine.encoded, localConfig]) input room
  have next : TM2.step (program () (constantBase result))
      (encoded input (.base ()) ⟨false, a, none, f :: fs⟩) =
      some (encoded input (loadPhase 0) ⟨false, a, some result, f :: fs⟩) := by
    simp [TM2.step, encoded, Alphabet.encoded, Alphabet.input, extendConfig,
      localConfig, program, constantBase, TM2.stepAux, status]
  have baseVal : Sav.baseVal (fun _ _ => result) (fun _ => result) f = result := by
    simp [Sav.baseVal]
  rw [baseVal]
  exact .step (encoded_bound input (.base ()) _ r room bound) next tail

end ComplexityOfGenerators.Simulation.SavitchMachine.AlphabetSearch
