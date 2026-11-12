import ComplexityOfGenerators.Examples.SATNative.EvaluationStep
import ComplexityOfGenerators.Examples.SATNative.EvaluationComplete

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem popped_represents (capacity active : ℕ) (certificate : List Symbol) (state : State) (s : Store)
    (represented : Represents capacity active certificate state s) :
    Represents capacity active certificate state (Function.update s 16 (s 16).tail) := by
  exact ⟨NativeBody.popped_represents capacity active state.parserState s represented.1,
    by simpa using represented.2.1, by simpa using represented.2.2⟩

theorem evaluationRoutine_represents {O : Type} (capacity active : ℕ) (certificate : List Symbol)
    (state : State) (s : Store) (represented : Represents capacity active certificate state s) :
    Represents capacity active certificate
      ((step capacity active certificate)^[(s 16).length] state) ((evaluationRoutine (O := O)).eval s) := by
  have one (state : State) (s : Store) (represented : Represents capacity active certificate state s) :
      Represents capacity active certificate (step capacity active certificate state)
        ((Routine.counted 16 (evaluationStep (O := O))).eval s) := by
    exact evaluationStep_represents capacity active certificate state _
      (popped_represents capacity active certificate state s represented)
  have iter (count : ℕ) : ∀ state s, Represents capacity active certificate state s →
      Represents capacity active certificate ((step capacity active certificate)^[count] state)
        ((Routine.counted 16 (evaluationStep (O := O))).eval^[count] s) := by
    induction count with
    | zero => intro state s h; exact h
    | succ count ih =>
      intro state s h
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply]
      exact ih _ _ (one state s h)
  exact iter _ state s represented

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
