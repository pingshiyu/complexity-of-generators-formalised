import ComplexityOfGenerators.Examples.SATNative.InverseNative.Header
import ComplexityOfGenerators.Examples.SATNative.BodyRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem liftLiteral_parserFrame {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active state ((liftLiteral (O := O) bit).eval s) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  have frame (j : Fin 32) (a : j ≠ 5) (b : j ≠ 9) (c : j ≠ 11) (d : j ≠ 21)
      (e : j ≠ 22) (f : j ≠ 23) (g : j ≠ 24) (h : j ≠ 31) :=
    liftLiteral_frame (O := O) bit s j a b c d e f g h
  simp [Represents, frame, word, cap, count, valid, inside, seen]

/-- A native inverse scan retains delimiters and applies the stored mask to
each parsed padded literal, consuming one mask bit per literal. -/
noncomputable def inverseStep {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  Routine.branch 2 fun head => match head with
  | none => Routine.skip
  | some tag => Routine.branch 17 fun inside =>
      if inside.isSome then
        if tag = .closeClause then bodyStep.seq (Routine.ofLocal (Local.push 21 .closeClause))
        else bodyStep.seq (liftLiteral bit)
      else bodyStep.seq
        (if tag = .openClause then Routine.ofLocal (Local.push 21 .openClause) else Routine.skip)

theorem pushed_parserFrame (capacity active : ℕ) (state : State) (s : Store) (symbol : Symbol)
    (represented : Represents capacity active state s) :
    Represents capacity active state (Function.update s 21 (symbol :: s 21)) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  simp [Represents, word, cap, count, valid, inside, seen]

theorem inverseStep_represents {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active (NativeBody.step capacity active state) ((inverseStep (O := O) bit).eval s) := by
  have saved := represented
  rcases saved with ⟨wordReg, _, _, _, insideReg, _⟩
  have parsed := NativeBody.bodyStep_represents (O := O) capacity active state s represented
  cases word : state.word with
  | nil => simpa [inverseStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval,
      NativeBody.step] using represented
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      by_cases opening : tag = .openClause
      · have pushed := pushed_parserFrame capacity active _ _ .openClause parsed
        simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushed
      · simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.eval] using parsed
    | true =>
      by_cases close : tag = .closeClause
      · have pushed := pushed_parserFrame capacity active _ _ .closeClause parsed
        simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, close,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushed
      · have substituted := liftLiteral_parserFrame (O := O) bit capacity active _ _ parsed
        simpa [inverseStep, Routine.branch, wordReg, word, insideReg, inside, close,
          Routine.seq] using substituted

theorem inverseStep_frame {O : Type} (bit : Bool) (s : Store) :
    (inverseStep (O := O) bit).eval s 16 = s 16 := by
  have body := bodyStep_frame (O := O) s
  have literal := liftLiteral_frame (O := O) bit ((bodyStep (O := O)).eval s) 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  cases head : (s 2).head? with
  | none => simp [inverseStep, Routine.branch, head, Routine.skip, Routine.ofLocal, Local.eval]
  | some tag =>
    cases inside : s 17 with
    | nil =>
      by_cases opening : tag = .openClause <;>
        simp [inverseStep, Routine.branch, head, inside, opening,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.eval_push, Local.eval, body]
    | cons mark rest =>
      by_cases close : tag = .closeClause <;>
        simp [inverseStep, Routine.branch, head, inside, close, Routine.seq,
          Routine.ofLocal, Local.eval_push, body, literal]

noncomputable def inverseRoutine {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  Routine.iterate 16 (inverseStep bit) (inverseStep_frame bit)

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
