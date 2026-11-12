import ComplexityOfGenerators.Examples.SATNative.EvaluationLoop
import ComplexityOfGenerators.Examples.SATNative.AssignmentBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem closeTruth_bound (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    stackBound budget (closeTruthCode.eval s) := by
  intro j
  cases truth : s 20 with
  | nil =>
    by_cases valid : j = 6 <;> by_cases value : j = 20 <;>
      simp [closeTruthCode, Local.eval, Local.pop, Action.apply, truth, valid, value, List.length_tail] <;>
      first | exact sizes _ | have := sizes 6; omega
  | cons head rest =>
    by_cases value : j = 20 <;>
      simp [closeTruthCode, Local.eval, Local.pop, Action.apply, truth, value] <;>
      first | exact sizes _ | have := sizes 20; simp only [truth, List.length_cons] at *; omega

theorem accumulate_frame (s : Store) (j : Fin 32) (different : j ≠ 20) :
    accumulateCode.eval s j = s j := by
  cases truth : s 26 <;> simp [accumulateCode, Local.eval, Local.write, Local.pop, Local.push, Action.apply, truth, different]

theorem evaluationStep_bound {O : Type} (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (s : Store) (represented : Represents capacity active certificate state s) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    stackBound budget ((evaluationStep (O := O)).eval s) := by
  have parsedBound := NativeBody.bodyStep_bound (O := O) capacity active state.parserState s represented.1 budget positive sizes cap count
  have syntaxSaved := represented.1
  rcases syntaxSaved with ⟨wordReg, _, _, _, insideReg, _⟩
  have truthReg := (evaluationStep_represents (O := O) capacity active certificate state s represented).2.2
  intro j
  by_cases valueReg : j = 20
  · subst j
    rw [truthReg]
    split_ifs <;> simp <;> omega
  · cases word : state.parserState.word with
    | nil => simpa [evaluationStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval] using sizes j
    | cons tag rest =>
      cases inside : state.parserState.inside with
      | false =>
        simpa [evaluationStep, Routine.branch, wordReg, word, insideReg, inside,
          Routine.seq, Routine.clear, valueReg] using parsedBound j
      | true =>
        by_cases close : tag = .closeClause
        · have closeBound := closeTruth_bound ((bodyStep (O := O)).eval s) budget parsedBound
          simpa [evaluationStep, Routine.branch, wordReg, word, insideReg, inside, close,
            Routine.seq, Routine.ofLocal] using closeBound j
        · have literalBound := NativeAssignment.literalValue_bound (O := O) ((bodyStep (O := O)).eval s) budget positive parsedBound
          simpa [evaluationStep, Routine.branch, wordReg, word, insideReg, inside, close,
            Routine.seq, Routine.ofLocal, accumulate_frame _ j valueReg] using literalBound j

noncomputable def stepConstant : ℕ :=
  NativeBody.stepConstant + 120 + NativeAssignment.valueCode.bound + closeTruthCode.bound + accumulateCode.bound

theorem evaluationStep_cost {O : Type} (capacity active : ℕ) (certificate : List Symbol) (state : State)
    (s : Store) (represented : Represents capacity active certificate state s) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) (cap : capacity ≤ budget) (count : active + 1 ≤ budget) :
    (evaluationStep (O := O)).cost s ≤ stepConstant * (budget + 1) := by
  have bodyCost := NativeBody.bodyStep_cost (O := O) capacity active state.parserState s represented.1 budget positive sizes cap count
  have bodyBound := NativeBody.bodyStep_bound (O := O) capacity active state.parserState s represented.1 budget positive sizes cap count
  have literalCost := NativeAssignment.literalValue_cost (O := O) ((bodyStep (O := O)).eval s) budget bodyBound
  have closeCost := closeTruthCode.ticks_le ((bodyStep (O := O)).eval s)
  have accumulateCost := accumulateCode.ticks_le ((NativeAssignment.literalValue (O := O)).eval ((bodyStep (O := O)).eval s))
  have memoryCost := bodyBound 20
  have syntaxSaved := represented.1
  rcases syntaxSaved with ⟨wordReg, _, _, _, insideReg, _⟩
  cases word : state.parserState.word with
  | nil =>
    simp only [evaluationStep, Routine.branch, wordReg, word, List.head?_nil, Routine.skip, Routine.ofLocal, Local.ticks]
    unfold stepConstant
    nlinarith
  | cons tag rest =>
    cases inside : state.parserState.inside with
    | false =>
      simp only [evaluationStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
        Bool.false_eq_true, ite_false, List.head?_nil, Option.isSome_none, Routine.seq, Routine.clear]
      unfold stepConstant
      nlinarith
    | true =>
      by_cases close : tag = .closeClause
      · simp only [evaluationStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          ite_true, Option.isSome_some, close, Routine.seq, Routine.ofLocal]
        unfold stepConstant
        nlinarith
      · simp only [evaluationStep, Routine.branch, wordReg, word, List.head?_cons, insideReg, inside,
          ite_true, Option.isSome_some, close, ite_false, Routine.seq, Routine.ofLocal]
        unfold stepConstant
        nlinarith

@[simp] theorem evaluationStep_randomFree {O : Type} : Command.RandomFree (evaluationStep (O := O)).command := by
  simp only [evaluationStep, Routine.randomFree_branch]
  intro head
  cases head with
  | none => simp
  | some tag =>
    simp only [Routine.randomFree_branch]
    intro inside
    by_cases present : inside.isSome <;> by_cases close : tag = .closeClause <;> simp [present, close]

@[simp] theorem evaluationRoutine_randomFree {O : Type} : Command.RandomFree (evaluationRoutine (O := O)).command := by
  simp [evaluationRoutine]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
