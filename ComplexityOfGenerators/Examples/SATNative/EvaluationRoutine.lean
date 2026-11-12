import ComplexityOfGenerators.Examples.SATNative.EvaluationModel
import ComplexityOfGenerators.Examples.SATNative.ParserPure

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

abbrev Store := NativeBody.Store

def Represents (capacity active : ℕ) (certificate : List Symbol) (state : State) (s : Store) : Prop :=
  NativeBody.Represents capacity active state.parserState s ∧ s 3 = certificate ∧
    s 20 = if state.clauseValue then [.one] else []

def closeTruthCode : Local Symbol 32 :=
  (Local.read 20 fun truth => if truth.isSome then .skip else Local.pop 6).seq (Local.pop 20)

def accumulateCode : Local Symbol 32 :=
  .read 26 fun truth => if truth.isSome then Local.write 20 .one else .skip

/-- The clause evaluator shares the native syntax parser. A literal's truth
value comes from a concrete unary certificate lookup, not from a semantic
oracle or an assumed machine. -/
noncomputable def evaluationStep {O : Type} : Routine Symbol O 32 :=
  Routine.branch 2 fun head => match head with
  | none => Routine.skip
  | some tag => Routine.branch 17 fun inside =>
      if inside.isSome then
        if tag = .closeClause then bodyStep.seq (Routine.ofLocal closeTruthCode)
        else bodyStep.seq (NativeAssignment.literalValue.seq (Routine.ofLocal accumulateCode))
      else bodyStep.seq (Routine.clear 20)

theorem literal_details {O : Type} (capacity active : ℕ) (state : NativeBody.State) (s : Store)
    (represented : NativeBody.Represents capacity active state s) :
    let output := ((NativeLiteral.literalRoutine (O := O)).rename subslots).eval s
    output 3 = s 3 ∧ output 5 = List.replicate (NativeLiteral.fieldState capacity state.word).count .one ∧
      output 11 = state.word.head?.toList := by
  dsimp only
  have here (j : Fin 16) :
      ((NativeLiteral.literalRoutine (O := O)).rename subslots).eval s (subslots j) =
        (NativeLiteral.literalRoutine (O := O)).eval
          (NativeLiteral.inputStore (s ∘ subslots) capacity active state.word state.valid) j := by
    rw [Routine.rename_eval_here, literal_input_eq capacity active state s represented]
  have certificate := here 3
  have count := here 5
  have tag := here 11
  rw [NativeLiteral.literalRoutine_eval] at certificate count tag
  refine ⟨?_, ?_, ?_⟩
  · simpa [subslots, NativeHeader.encoded, NativeLiteral.indexFrame, NativeLiteral.scaffold,
      NativeLiteral.checked, NativeHeader.restrict, Function.comp_def] using certificate
  · simpa [subslots, NativeHeader.encoded, NativeLiteral.indexFrame, NativeLiteral.scaffold,
      NativeLiteral.checked, NativeHeader.restrict, Function.comp_def] using count
  · simpa [subslots, NativeHeader.encoded, NativeLiteral.indexFrame, NativeLiteral.scaffold,
      NativeLiteral.checked, NativeHeader.restrict, Function.comp_def] using tag

theorem bodyStep_certificate {O : Type} (capacity active : ℕ) (state : NativeBody.State) (s : Store)
    (represented : NativeBody.Represents capacity active state s) :
    (bodyStep (O := O)).eval s 3 = s 3 := by
  rcases represented with ⟨wordReg, cap, count, valid, insideReg, seen⟩
  have repr : NativeBody.Represents capacity active state s := ⟨wordReg, cap, count, valid, insideReg, seen⟩
  cases word : state.word with
  | nil => simp [bodyStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval]
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      by_cases opening : tag = .openClause <;>
        simp [bodyStep, Routine.branch, wordReg, word, insideReg, inside, Routine.ofLocal,
          outsideCode, Local.eval, Local.pop, Local.push, Action.apply, opening]
    | true =>
      by_cases close : tag = .closeClause
      · cases mark : state.nonempty <;>
          simp [bodyStep, Routine.branch, wordReg, word, insideReg, inside, close, Routine.ofLocal,
            closeCode, Local.eval, Local.pop, Action.apply, seen, mark]
      · have same := (literal_details (O := O) capacity active state s repr).1
        simpa [bodyStep, Routine.branch, wordReg, word, insideReg, inside, close,
          Routine.seq, Routine.ofLocal, Local.eval_write] using same

theorem bodyStep_truthFrame {O : Type} (s : Store) : (bodyStep (O := O)).eval s 20 = s 20 := by
  cases head : (s 2).head? with
  | none => simp [bodyStep, Routine.branch, head, Routine.skip, Routine.ofLocal, Local.eval]
  | some tag =>
    cases inside : s 17 with
    | nil =>
      by_cases opening : tag = .openClause <;>
        simp [bodyStep, Routine.branch, head, inside, Routine.ofLocal, outsideCode,
          Local.eval, Local.pop, Local.push, Action.apply, opening]
    | cons mark tail =>
      by_cases close : tag = .closeClause
      · cases seen : s 18 <;>
          simp [bodyStep, Routine.branch, head, inside, close, Routine.ofLocal, closeCode,
            Local.eval, Local.pop, Action.apply, seen]
      · have frame := Routine.rename_eval_frame (NativeLiteral.literalRoutine (O := O)) subslots s 20
          (by intro i equal; have := congrArg Fin.val equal; simp only [subslots_val] at this; omega)
        simpa [bodyStep, Routine.branch, head, inside, close, Routine.seq, Routine.ofLocal, Local.eval_write] using frame

theorem literalValue_parserFrame {O : Type} (capacity active : ℕ) (state : NativeBody.State) (s : Store)
    (represented : NativeBody.Represents capacity active state s) :
    NativeBody.Represents capacity active state ((NativeAssignment.literalValue (O := O)).eval s) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  have frame (j : Fin 32) (a : j ≠ 9) (b : j ≠ 22) (c : j ≠ 23) (d : j ≠ 24) (e : j ≠ 25) (f : j ≠ 26) :=
    NativeAssignment.literalValue_frame (O := O) s j a b c d e f
  simp [NativeBody.Represents, frame, word, cap, count, valid, inside, seen]

theorem evaluationStep_frame {O : Type} (s : Store) : (evaluationStep (O := O)).eval s 16 = s 16 := by
  have source := bodyStep_frame (O := O) s
  have selected := NativeAssignment.literalValue_frame (O := O) ((bodyStep (O := O)).eval s) 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  cases head : (s 2).head? with
  | none => simp [evaluationStep, Routine.branch, head, Routine.skip, Routine.ofLocal, Local.eval]
  | some tag =>
    cases inside : s 17 with
    | nil => simp [evaluationStep, Routine.branch, head, inside, Routine.seq, Routine.clear, source]
    | cons mark rest =>
      by_cases close : tag = .closeClause
      · cases truth : (bodyStep (O := O)).eval s 20 <;>
          simp [evaluationStep, Routine.branch, head, inside, close, Routine.seq, Routine.ofLocal,
            closeTruthCode, Local.eval, Local.pop, Action.apply, truth, source]
      · cases truth : (NativeAssignment.literalValue (O := O)).eval ((bodyStep (O := O)).eval s) 26 <;>
          simp [evaluationStep, Routine.branch, head, inside, close, Routine.seq, Routine.ofLocal,
            accumulateCode, Local.eval, Local.write, Local.pop, Local.push, Action.apply, truth, selected, source]

noncomputable def evaluationRoutine {O : Type} : Routine Symbol O 32 :=
  Routine.iterate 16 evaluationStep evaluationStep_frame

end ComplexityOfGenerators.Examples.PaddedCNF.NativeEvaluation
