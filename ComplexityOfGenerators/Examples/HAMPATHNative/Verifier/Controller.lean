import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.BaseTest
import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Components
import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Model
import ComplexityOfGenerators.Simulation.WordStack.BooleanReturn

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] loop body

def inputPrepare : Routine Symbol Unit 64 :=
  (Routine.transfer 0 32 (by decide) id).seq
    ((Routine.transfer 1 33 (by decide) id).seq
      (Routine.assign 33 34 38 (by decide) (by decide) (by decide) (fun _ => .bit true)))

def loaded (word certificate : List Symbol) : Memory Symbol Unit 64 :=
  ⟨(), 0, 0, [], Function.update (Function.update (fun _ => []) 0 word.reverse) 1 certificate.reverse⟩

def prepared (word certificate : List Symbol) : Store := inputPrepare.eval (loaded word certificate).store

theorem prepared_fields (word certificate : List Symbol) :
    prepared word certificate 32 = word ∧ prepared word certificate 33 = certificate ∧
      (prepared word certificate 34).length = certificate.length ∧
      StoreBound (prepared word certificate) (word.length + certificate.length) := by
  have values : prepared word certificate = Function.update (Function.update (Function.update
      (Function.update (Function.update (fun _ => []) 0 []) 1 []) 32 word) 33 certificate) 34
        (List.replicate certificate.length (.bit true)) := by
    funext j
    by_cases a : j = 0 <;> by_cases b : j = 1 <;> by_cases c : j = 32 <;>
      by_cases d : j = 33 <;> by_cases e : j = 34 <;> by_cases f : j = 38 <;>
      simp [prepared, loaded, inputPrepare, Routine.seq, Routine.transfer, Routine.assign_eval, List.map_const', a, b, c, d, e, f]
  rw [values]
  refine ⟨by simp, by simp, by simp, ?_⟩
  intro j
  by_cases a : j = 32 <;> by_cases b : j = 33 <;> by_cases c : j = 34 <;>
    simp [a, b, c] <;> omega

noncomputable def routine : Routine Symbol Unit 64 := inputPrepare.seq (loop.seq baseTest)

def checks : Program.BooleanChecks Symbol 64 :=
  ![(33, fun head => !head.isSome), (44, fun head => head.isSome), (34, fun _ => true)]

theorem checks_baseTest (s : Store) : Program.checksPass checks (baseTest.eval s) = accepts (view s) := by
  have remaining : baseTest.eval s 33 = s 33 := baseTest_frame s 33 (by decide) (by decide) (by decide)
  change (!((baseTest.eval s 33).head?.isSome) && (baseTest.eval s 44).head?.isSome && true) = _
  rw [remaining, baseTest_flag]
  simp only [Bool.and_true, accepts, view]
  cases current : decide (s 32 = baseWord) <;> cases certificate : s 33 <;> simp [flag, current, certificate]

theorem routine_decides (word certificate : List Symbol) :
    Program.checksPass checks (routine.eval (loaded word certificate).store) = value word certificate := by
  change Program.checksPass checks (baseTest.eval (loop.eval (prepared word certificate))) = _
  rw [checks_baseTest, loop_view]
  obtain ⟨current, remaining, clock, _⟩ := prepared_fields word certificate
  rw [clock]
  have starting : view (prepared word certificate) = (⟨word, certificate⟩ : State) := by
    apply congrArg₂ State.mk <;> assumption
  rw [starting]
  rfl

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
