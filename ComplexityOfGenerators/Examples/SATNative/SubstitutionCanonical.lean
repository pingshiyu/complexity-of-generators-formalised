import ComplexityOfGenerators.Examples.SATNative.SubstitutionFrames
import ComplexityOfGenerators.Examples.SATNative.EvaluationStep

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeBody
open NativeAssignment

set_option backward.isDefEq.respectTransparency false

theorem encoded_head (capacity : ℕ) (literal : Literal) (rest : List Symbol) :
    (literal.encode capacity ++ rest).head? = some (literalTag literal) := by
  cases literal with
  | constant value => cases value <;> simp [Literal.encode, literalTag]
  | var index sign => cases sign <;> simp [Literal.encode, literalTag]

theorem encoded_count {capacity active : ℕ} (bound : active ≤ capacity) (literal : Literal)
    (valid : literal.valid active) (rest : List Symbol) :
    (NativeLiteral.fieldState capacity (literal.encode capacity ++ rest)).count = literalIndex literal := by
  cases literal with
  | constant value =>
    cases value <;>
      simpa [Literal.encode, literalIndex, List.append_assoc] using congrArg NativeHeader.ScanState.count
        (NativeLiteral.field_canonical capacity 0 (Nat.zero_le _) _ rest)
  | var index sign =>
    have fits := valid.2.trans bound
    cases sign <;>
      simpa [Literal.encode, literalIndex, List.append_assoc] using congrArg NativeHeader.ScanState.count
        (NativeLiteral.field_canonical capacity index fits _ rest)

theorem literalTag_not_close (literal : Literal) : literalTag literal ≠ .closeClause := by
  cases literal with
  | constant value => cases value <;> simp [literalTag]
  | var index sign => cases sign <;> simp [literalTag]

set_option maxHeartbeats 800000 in
theorem substitutionStep_literal {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (literal : Literal) (valid : literal.valid active) (rest : List Symbol) (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨literal.encode capacity ++ rest, true, seen, enabled⟩ s) :
    let output := (substitutionStep (O := O) bit).eval s
    Represents capacity active ⟨rest, true, true, enabled⟩ output ∧
      output 21 = ((literal.substitute active bit).encode capacity).reverse ++ s 21 := by
  dsimp only
  let state : State := ⟨literal.encode capacity ++ rest, true, seen, enabled⟩
  have parsedRep := bodyStep_represents (O := O) capacity active state s represented
  have first : state.word = literalTag literal :: state.word.tail := by
    cases literal with
    | constant value => cases value <;> simp [state, Literal.encode, literalTag]
    | var index sign => cases sign <;> simp [state, Literal.encode, literalTag]
  have details := NativeEvaluation.bodyStep_literal_details (O := O) capacity active state s represented
    (literalTag literal) state.word.tail first rfl (literalTag_not_close literal)
  have indexField : (bodyStep (O := O)).eval s 5 = List.replicate (literalIndex literal) .one := by
    simpa only [state, encoded_count bound literal valid rest] using details.1
  have tagField : (bodyStep (O := O)).eval s 11 = [literalTag literal] := by
    simpa only [state, encoded_head, Option.toList_some] using details.2
  have transformed := substituteLiteral_buffer_of_fields (O := O) bit ((bodyStep (O := O)).eval s) capacity active literal
    parsedRep.2.1 parsedRep.2.2.1 indexField tagField
  rw [bodyStep_upperFrame (O := O) s 21 (by decide) (by decide) (by decide)] at transformed
  refine ⟨?_, ?_⟩
  · have representedNext := substitutionStep_represents (O := O) bit capacity active state s represented
    simpa only [state, NativeBody.step_literal bound literal valid rest seen enabled] using representedNext
  · have wordReg := represented.1
    have insideReg : s 17 = [.one] := represented.2.2.2.2.1
    have header : (s 2).head? = some (literalTag literal) := by rw [wordReg]; exact encoded_head capacity literal rest
    simpa [substitutionStep, Routine.branch, header, insideReg, literalTag_not_close, Routine.seq] using transformed

theorem substitutionStep_open {O : Type} (bit : Bool) (capacity active : ℕ) (rest : List Symbol)
    (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨.openClause :: rest, false, seen, enabled⟩ s) :
    let output := (substitutionStep (O := O) bit).eval s
    Represents capacity active ⟨rest, true, false, enabled⟩ output ∧ output 21 = .openClause :: s 21 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simpa [NativeBody.step] using substitutionStep_represents (O := O) bit capacity active _ s represented
  · have frame := bodyStep_upperFrame (O := O) s 21 (by decide) (by decide) (by decide)
    simp [substitutionStep, Routine.branch, represented.1, represented.2.2.2.2.1,
      Routine.seq, Routine.ofLocal, Local.eval_push, frame]

theorem substitutionStep_close {O : Type} (bit : Bool) (capacity active : ℕ) (rest : List Symbol)
    (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨.closeClause :: rest, true, seen, enabled⟩ s) :
    let output := (substitutionStep (O := O) bit).eval s
    Represents capacity active ⟨rest, false, false, enabled && seen⟩ output ∧ output 21 = .closeClause :: s 21 := by
  dsimp only
  refine ⟨?_, ?_⟩
  · simpa [NativeBody.step] using substitutionStep_represents (O := O) bit capacity active _ s represented
  · have frame := bodyStep_upperFrame (O := O) s 21 (by decide) (by decide) (by decide)
    simp [substitutionStep, Routine.branch, represented.1, represented.2.2.2.2.1,
      Routine.seq, Routine.ofLocal, Local.eval_push, frame]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
