import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Computability
import ComplexityOfGenerators.Examples.HAMPATHNative.WidthComputability
import ComplexityOfGenerators.Simulation.WordStack.RegisterEmbedding
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 64

def slots : Fin 32 ↪ Fin 64 := ⟨fun i => ⟨i.val, by omega⟩, by intro i j same; exact Fin.ext (congrArg (fun x : Fin 64 => x.val) same)⟩

def lowRegisters : List (Fin 64) := (List.finRange 64).filter (fun j => j.val < 32)

def argsSetup : Routine Symbol Unit 64 :=
  (Routine.clearMany lowRegisters).seq
    ((Routine.assign 32 37 38 (by decide) (by decide) (by decide) id).seq
      ((Routine.transfer 37 0 (by decide) id).seq
        ((Routine.assign 36 37 38 (by decide) (by decide) (by decide) id).seq
          (Routine.transfer 37 1 (by decide) id))))

theorem argsSetup_owned (s : Store) :
    argsSetup.eval s ∘ slots = Reduction.loadedStore (s 32) (s 36) := by
  funext j
  have low : (slots j).val < 32 := j.isLt
  have a : slots j ≠ (32 : Fin 64) := by intro h; have := congrArg Fin.val h; simp [slots] at this; omega
  have b : slots j ≠ (36 : Fin 64) := by intro h; have := congrArg Fin.val h; simp [slots] at this; omega
  have c : slots j ≠ (37 : Fin 64) := by intro h; have := congrArg Fin.val h; simp [slots] at this; omega
  have d : slots j ≠ (38 : Fin 64) := by intro h; have := congrArg Fin.val h; simp [slots] at this; omega
  have zero : slots j = 0 ↔ j = 0 := by constructor <;> intro h <;> apply Fin.ext <;> simpa [slots] using congrArg Fin.val h
  have one : slots j = 1 ↔ j = 1 := by constructor <;> intro h <;> apply Fin.ext <;> simpa [slots] using congrArg Fin.val h
  simp [argsSetup, Routine.seq, Routine.assign_eval, Routine.transfer, Routine.clearMany_eval,
    lowRegisters, low, Reduction.loadedStore, Function.comp_def, Function.update_apply,
    a, b, c, d, zero, one]

theorem argsSetup_frame (s : Store) (j : Fin 64) (high : 32 ≤ j.val)
    (different37 : j ≠ 37) (different38 : j ≠ 38) : argsSetup.eval s j = s j := by
  have notLow : ¬j.val < 32 := by omega
  have zero : j ≠ 0 := by intro h; simp [h] at high
  have one : j ≠ 1 := by intro h; simp [h] at high
  simp [argsSetup, Routine.seq, Routine.assign_eval, Routine.transfer, Routine.clearMany_eval,
    lowRegisters, notLow, Function.update_apply, different37, different38, zero, one]

noncomputable def invoke (body : Routine Symbol Unit 32) (result : Fin 32)
    (output : Fin 64) (high : 32 ≤ output.val) (scratch : output ≠ 40) : Routine Symbol Unit 64 :=
  argsSetup.seq ((body.rename slots).seq
    (Routine.assign (slots result) output 40
      (by intro h; have := congrArg Fin.val h; simp [slots] at this; have := result.isLt; omega)
      (by intro h; have := congrArg Fin.val h; simp [slots] at this; have := result.isLt; omega)
      scratch id))

theorem invoke_value (body : Routine Symbol Unit 32) (result : Fin 32)
    (output : Fin 64) (high : 32 ≤ output.val) (scratch : output ≠ 40) (s : Store) :
    (invoke body result output high scratch).eval s output =
      body.eval (Reduction.loadedStore (s 32) (s 36)) result := by
  simp only [invoke, Routine.seq, Routine.assign_eval, Function.update_self, List.map_id]
  rw [Routine.rename_eval_here, argsSetup_owned]

theorem invoke_frame (body : Routine Symbol Unit 32) (result : Fin 32)
    (output : Fin 64) (high : 32 ≤ output.val) (scratch : output ≠ 40) (s : Store)
    (j : Fin 64) (outside : 32 ≤ j.val) (a : j ≠ 37) (b : j ≠ 38)
    (c : j ≠ 40) (d : j ≠ output) :
    (invoke body result output high scratch).eval s j = s j := by
  have away : ∀ i, j ≠ slots i := by
    intro i same
    have := congrArg Fin.val same
    simp [slots] at this
    have := i.isLt
    omega
  simp only [invoke, Routine.seq, Routine.assign_eval, Function.update_of_ne d, Function.update_of_ne c]
  rw [Routine.rename_eval_frame body slots _ j away]
  exact argsSetup_frame s j outside a b

theorem argsSetup_randomFree : Command.RandomFree argsSetup.command := by simp [argsSetup]

theorem invoke_randomFree (body : Routine Symbol Unit 32) (result : Fin 32)
    (output : Fin 64) (high : 32 ≤ output.val) (scratch : output ≠ 40)
    (pure : Command.RandomFree body.command) :
    Command.RandomFree (invoke body result output high scratch).command := by
  simp only [invoke, Routine.randomFree_seq]
  exact ⟨argsSetup_randomFree, Routine.randomFree_rename body slots pure, by simp⟩

attribute [irreducible] invoke

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
