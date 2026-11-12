import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Calls
import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Value

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] widthRoutine Reduction.routine

noncomputable def widthCall : Routine Symbol Unit 64 :=
  (Routine.clear 36).seq (invoke widthRoutine 19 39 (by decide) (by decide))

def splitLabel : Routine Symbol Unit 64 :=
  (Routine.clear 35).seq
    ((Blocks.routine 39 33 35 (by decide) (by decide)).seq (Routine.transfer 35 36 (by decide) id))

noncomputable def reduceCall : Routine Symbol Unit 64 :=
  invoke (Reduction.routine (O := Unit)) 31 32 (by decide) (by decide)

noncomputable def activeStep : Routine Symbol Unit 64 := widthCall.seq (splitLabel.seq reduceCall)

noncomputable def body : Routine Symbol Unit 64 :=
  Routine.branch 33 fun head => if head.isSome then activeStep else Routine.skip

def view (s : Store) : State := ⟨s 32, s 33⟩

theorem width_loaded (word : List Symbol) :
    Reduction.loadedStore word [] = (loaded word ([] : List Unit)).store := by
  funext j
  simp [Reduction.loadedStore, loaded]

theorem widthCall_value (s : Store) :
    widthCall.eval s 39 = List.replicate (wordWidth (s 32)) (.bit true) := by
  change (invoke widthRoutine 19 39 (by decide) (by decide)).eval ((Routine.clear (O := Unit) 36).eval s) 39 = _
  rw [invoke_value]
  simp only [Routine.clear, Function.update_self, Function.update_of_ne (by decide : (32 : Fin 64) ≠ 36)]
  rw [width_loaded, widthRoutine_value]

theorem widthCall_frame (s : Store) (j : Fin 64) (high : 32 ≤ j.val)
    (a : j ≠ 36) (b : j ≠ 37) (c : j ≠ 38) (d : j ≠ 39) (e : j ≠ 40) :
    widthCall.eval s j = s j := by
  change (invoke widthRoutine 19 39 (by decide) (by decide)).eval ((Routine.clear (O := Unit) 36).eval s) j = _
  rw [invoke_frame _ _ _ _ _ _ j high b c e d]
  exact Function.update_of_ne a ..

theorem widthCall_label (s : Store) : widthCall.eval s 36 = [] := by
  change (invoke widthRoutine 19 39 (by decide) (by decide)).eval ((Routine.clear (O := Unit) 36).eval s) 36 = _
  rw [invoke_frame _ _ _ _ _ _ 36 (by decide) (by decide) (by decide) (by decide) (by decide)]
  simp [Routine.clear]

theorem splitLabel_fields (s : Store) (empty : s 36 = []) :
    splitLabel.eval s 32 = s 32 ∧
    splitLabel.eval s 33 = (s 33).drop (s 39).length ∧
    splitLabel.eval s 36 = (s 33).take (s 39).length ∧
    splitLabel.eval s 34 = s 34 := by
  simp [splitLabel, Routine.seq, Routine.clear, Blocks.routine_eval (O := Unit) (39 : Fin 64) 33 35 (by decide) (by decide) (by decide),
    Routine.transfer, empty]

theorem reduceCall_value (s : Store) : reduceCall.eval s 32 = wordReduce (s 32) (s 36) := by
  rw [reduceCall, invoke_value, Reduction.routine_value]

theorem reduceCall_frame (s : Store) (j : Fin 64) (high : 32 ≤ j.val)
    (a : j ≠ 32) (b : j ≠ 37) (c : j ≠ 38) (d : j ≠ 40) :
    reduceCall.eval s j = s j := invoke_frame _ _ _ _ _ s j high b c d a

theorem activeStep_view (s : Store) : view (activeStep.eval s) =
    ⟨wordReduce (s 32) ((s 33).take (wordWidth (s 32))), (s 33).drop (wordWidth (s 32))⟩ := by
  let a := widthCall.eval s
  let b := splitLabel.eval a
  have fields := splitLabel_fields a (widthCall_label s)
  change b 32 = a 32 ∧ b 33 = (a 33).drop (a 39).length ∧ b 36 = (a 33).take (a 39).length ∧ b 34 = a 34 at fields
  have current : a 32 = s 32 := widthCall_frame s 32 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have remaining : a 33 = s 33 := widthCall_frame s 33 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have width : (a 39).length = wordWidth (s 32) := by simp only [a, widthCall_value, List.length_replicate]
  apply congrArg₂ State.mk
  · change reduceCall.eval b 32 = _
    rw [reduceCall_value, fields.1, fields.2.2.1, current, remaining, width]
  · change reduceCall.eval b 33 = _
    rw [reduceCall_frame b 33 (by decide) (by decide) (by decide) (by decide) (by decide), fields.2.1, remaining, width]

theorem activeStep_clock (s : Store) : activeStep.eval s 34 = s 34 := by
  change reduceCall.eval (splitLabel.eval (widthCall.eval s)) 34 = _
  rw [reduceCall_frame _ 34 (by decide) (by decide) (by decide) (by decide) (by decide),
    (splitLabel_fields _ (widthCall_label s)).2.2.2]
  exact widthCall_frame s 34 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem body_view (s : Store) : view (body.eval s) = step (view s) := by
  cases remaining : s 33 with
  | nil => simp [body, Routine.branch, remaining, Routine.skip, Routine.ofLocal, step, view]
  | cons head tail =>
      simp only [body, Routine.branch, remaining, List.head?_cons, Option.isSome_some, ite_true]
      rw [activeStep_view]
      simp [step, view, remaining]

theorem body_clock (s : Store) : body.eval s 34 = s 34 := by
  simp only [body, Routine.branch]
  split
  · exact activeStep_clock s
  · rfl

noncomputable def loop : Routine Symbol Unit 64 := Routine.iterate 34 body body_clock

theorem counted_view (s : Store) : view ((Routine.counted 34 body).eval s) = step (view s) := by
  change view (body.eval ((Routine.ofLocal (Local.pop 34)).eval s)) = _
  rw [body_view]
  rfl

theorem iterate_view (count : ℕ) (s : Store) :
    view ((Routine.counted 34 body).eval^[count] s) = step^[count] (view s) := by
  induction count generalizing s with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply, ih, counted_view, Function.iterate_succ_apply]

theorem loop_view (s : Store) : view (loop.eval s) = step^[(s 34).length] (view s) := iterate_view _ s

end ComplexityOfGenerators.Examples.HAMPATH.Native.Verifier
