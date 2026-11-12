import ComplexityOfGenerators.Simulation.StarPaths.DP
import ComplexityOfGenerators.Simulation.StarPaths.ProposalComplete
import ComplexityOfGenerators.Simulation.StarPaths.ValidationComplete

namespace ComplexityOfGenerators.Simulation.StarPaths
open WordStack
set_option backward.isDefEq.respectTransparency true
set_option maxHeartbeats 400000
attribute [local irreducible] outerBody stageSetup stageRoutine appendEntry dpRoutine prepare
  proposalCoin proposalLoop proposalSetup proposalFinish proposalRoutine
  validationBody validationFactor validationLoop validationSetup validationRoutine

theorem outerBody_frame_upper {O : Type} (j : Fin 35) (upper : 13 ≤ j.val) :
    (outerBody (O := O)).Fixes j := by
  unfold outerBody
  exact (WordStack.Routine.fixes_push 1 j Symbol.unit (by omega)).seq
    ((stageSetup_frame j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)).seq
      ((stageRoutine_frame j (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega)).seq
          (appendEntry_frame j (by omega) (by omega))))

theorem prepare_frame {O : Type} (j : Fin 35) (master : j = 17 ∨ j = 22 ∨ j = 25) :
    (prepare (O := O)).Fixes j := by
  intro s
  rcases master with rfl | rfl | rfl <;>
    simp [prepare,WordStack.Routine.seq,WordStack.Routine.clearMany_eval,owned,WordStack.Routine.assign_eval,
      WordStack.Routine.ofLocal,Local.eval_push]

theorem dpRoutine_frame {O : Type} (j : Fin 35) (master : j = 17 ∨ j = 22 ∨ j = 25) :
    (dpRoutine (O := O)).Fixes j := by
  have upper : 13 ≤ j.val := by rcases master with rfl | rfl | rfl <;> decide
  unfold dpRoutine
  exact (prepare_frame j master).seq
    (WordStack.Routine.Fixes.iterate 0 outerBody outerBody_frame j (by omega) (outerBody_frame_upper j upper))

theorem proposalSetup_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 18) (c : j ≠ 31) :
    (proposalSetup (O := O)).Fixes j := by
  unfold proposalSetup
  exact (WordStack.Routine.fixes_clear 31 j c).seq
    ((WordStack.Routine.fixes_assign 22 18 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit) j b a).seq
      (WordStack.Routine.fixes_pop 18 j b))

theorem proposalRoutine_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 17) (c : j ≠ 18) (d : j ≠ 31) :
    (proposalRoutine (O := O)).Fixes j := by
  have loop : (proposalLoop (O := O)).Fixes j := by
    unfold proposalLoop
    exact WordStack.Routine.Fixes.iterate 18 proposalCoin (proposalCoin_frame 18 (by decide) (by decide))
      j c (proposalCoin_frame j b d)
  unfold proposalRoutine
  apply WordStack.Routine.Fixes.seq (proposalSetup_frame j a c d)
  unfold proposalFinish
  apply WordStack.Routine.Fixes.branch
  intro size
  split_ifs
  · exact (WordStack.Routine.fixes_push 31 j Symbol.unit d).seq
      (loop.seq (WordStack.Routine.fixes_push 31 j Symbol.cut d))
  · exact WordStack.Routine.fixes_skip j

theorem validationSetup_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 16) (c : j ≠ 18) (d : j ≠ 20) :
    (validationSetup (O := O)).Fixes j := by
  unfold validationSetup
  exact (WordStack.Routine.fixes_assign 31 16 12 (by decide) (by decide) (by decide) id j b a).seq
    ((WordStack.Routine.fixes_assign 22 18 12 (by decide) (by decide) (by decide) (fun _ => Symbol.unit) j c a).seq
      ((WordStack.Routine.fixes_clear 20 j d).seq (WordStack.Routine.fixes_push 20 j Symbol.present d)))

theorem validationRoutine_frame {O : Type} (j : Fin 35) (a : j ≠ 12) (b : j ≠ 16) (c : j ≠ 18)
    (d : j ≠ 19) (e : j ≠ 20) (f : j ≠ 21) (g : j ≠ 23) :
    (validationRoutine (O := O)).Fixes j := by
  unfold validationRoutine
  apply WordStack.Routine.Fixes.seq (validationSetup_frame j a b c e)
  unfold validationLoop
  exact WordStack.Routine.Fixes.iterate 18 validationBody
    (validationBody_frame 18 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide))
    j c (validationBody_frame j a b d e f g)

end ComplexityOfGenerators.Simulation.StarPaths
