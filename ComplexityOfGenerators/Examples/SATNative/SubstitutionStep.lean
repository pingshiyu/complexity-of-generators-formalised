import ComplexityOfGenerators.Examples.SATNative.SubstitutionHeader
import ComplexityOfGenerators.Examples.SATNative.BodyRoutine

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody

set_option backward.isDefEq.respectTransparency false

theorem substituteLiteral_frame {O : Type} (bit : Bool) (s : Store) (j : Fin 32)
    (index : j ≠ 5) (scratch : j ≠ 9) (tag : j ≠ 11) (buffer : j ≠ 21)
    (copy : j ≠ 22) (counter : j ≠ 23) (discarded : j ≠ 24) (flag : j ≠ 27) :
    (substituteLiteral (O := O) bit).eval s j = s j := by
  change (emitLiteral (O := O)).eval ((rewriteLiteral (O := O) bit).eval s) j = _
  rw [emitLiteral_frame _ _ scratch buffer copy counter discarded,
    rewriteLiteral_frame bit s j index scratch tag copy counter flag]

theorem substituteLiteral_parserFrame {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active state ((substituteLiteral (O := O) bit).eval s) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  have frame (j : Fin 32) (a : j ≠ 5) (b : j ≠ 9) (c : j ≠ 11) (d : j ≠ 21)
      (e : j ≠ 22) (f : j ≠ 23) (g : j ≠ 24) (h : j ≠ 27) :=
    substituteLiteral_frame (O := O) bit s j a b c d e f g h
  simp [Represents, frame, word, cap, count, valid, inside, seen]

/-- Streaming checked substitution: delimiter cases append one delimiter,
while literal cases call the concrete padded-record transformer. -/
noncomputable def substitutionStep {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  Routine.branch 2 fun head => match head with
  | none => Routine.skip
  | some tag => Routine.branch 17 fun inside =>
      if inside.isSome then
        if tag = .closeClause then bodyStep.seq (Routine.ofLocal (Local.push 21 .closeClause))
        else bodyStep.seq (substituteLiteral bit)
      else bodyStep.seq
        (if tag = .openClause then Routine.ofLocal (Local.push 21 .openClause) else Routine.skip)

theorem pushed_parserFrame (capacity active : ℕ) (state : State) (s : Store) (symbol : Symbol)
    (represented : Represents capacity active state s) :
    Represents capacity active state (Function.update s 21 (symbol :: s 21)) := by
  rcases represented with ⟨word, cap, count, valid, inside, seen⟩
  simp [Represents, word, cap, count, valid, inside, seen]

theorem substitutionStep_represents {O : Type} (bit : Bool) (capacity active : ℕ) (state : State) (s : Store)
    (represented : Represents capacity active state s) :
    Represents capacity active (NativeBody.step capacity active state) ((substitutionStep (O := O) bit).eval s) := by
  have saved := represented
  rcases saved with ⟨wordReg, _, _, _, insideReg, _⟩
  have parsed := NativeBody.bodyStep_represents (O := O) capacity active state s represented
  cases word : state.word with
  | nil => simpa [substitutionStep, Routine.branch, wordReg, word, Routine.skip, Routine.ofLocal, Local.eval,
      NativeBody.step] using represented
  | cons tag rest =>
    cases inside : state.inside with
    | false =>
      by_cases opening : tag = .openClause
      · have pushed := pushed_parserFrame capacity active _ _ .openClause parsed
        simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushed
      · simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, opening,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.eval] using parsed
    | true =>
      by_cases close : tag = .closeClause
      · have pushed := pushed_parserFrame capacity active _ _ .closeClause parsed
        simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, close,
          Routine.seq, Routine.ofLocal, Local.eval_push] using pushed
      · have substituted := substituteLiteral_parserFrame (O := O) bit capacity active _ _ parsed
        simpa [substitutionStep, Routine.branch, wordReg, word, insideReg, inside, close,
          Routine.seq] using substituted

theorem substitutionStep_frame {O : Type} (bit : Bool) (s : Store) :
    (substitutionStep (O := O) bit).eval s 16 = s 16 := by
  have body := bodyStep_frame (O := O) s
  have literal := substituteLiteral_frame (O := O) bit ((bodyStep (O := O)).eval s) 16
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  cases head : (s 2).head? with
  | none => simp [substitutionStep, Routine.branch, head, Routine.skip, Routine.ofLocal, Local.eval]
  | some tag =>
    cases inside : s 17 with
    | nil =>
      by_cases opening : tag = .openClause <;>
        simp [substitutionStep, Routine.branch, head, inside, opening,
          Routine.seq, Routine.skip, Routine.ofLocal, Local.eval_push, Local.eval, body]
    | cons mark rest =>
      by_cases close : tag = .closeClause <;>
        simp [substitutionStep, Routine.branch, head, inside, close, Routine.seq,
          Routine.ofLocal, Local.eval_push, body, literal]

noncomputable def substitutionRoutine {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  Routine.iterate 16 (substitutionStep bit) (substitutionStep_frame bit)

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
