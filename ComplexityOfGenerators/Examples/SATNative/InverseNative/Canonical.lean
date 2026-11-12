import ComplexityOfGenerators.Examples.SATNative.InverseNative.Step
import ComplexityOfGenerators.Examples.SATNative.SubstitutionCanonical

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack
open NativeBody
open NativeAssignment (literalIndex literalTag)
open NativeSubstitution (encoded_head encoded_count literalTag_not_close bodyStep_upperFrame)

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000 in
theorem inverseStep_literal {O : Type} (bit : Bool) {capacity active : ℕ} (bound : active ≤ capacity)
    (literal : Literal) (valid : literal.valid active) (rest : List Symbol) (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨literal.encode capacity ++ rest, true, seen, enabled⟩ s)
    (choices : List Bool) (mask : s 31 = choices.map bitSymbol) :
    let output := (inverseStep (O := O) bit).eval s
    Represents capacity active ⟨rest, true, true, enabled⟩ output ∧
      output 31 = choices.tail.map bitSymbol ∧
      output 21 = ((literal.lift active bit (choices.headD false)).encode capacity).reverse ++ s 21 := by
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
  have maskField : (bodyStep (O := O)).eval s 31 = choices.map bitSymbol :=
    (bodyStep_upperFrame (O := O) s 31 (by decide) (by decide) (by decide)).trans mask
  have transformed := liftLiteral_buffer_of_fields (O := O) bit ((bodyStep (O := O)).eval s) capacity active literal choices
    maskField parsedRep.2.1 parsedRep.2.2.1 indexField tagField
  rw [bodyStep_upperFrame (O := O) s 21 (by decide) (by decide) (by decide)] at transformed
  have consumed := liftLiteral_mask (O := O) bit ((bodyStep (O := O)).eval s)
  rw [maskField, ← List.map_tail] at consumed
  have wordReg := represented.1
  have insideReg : s 17 = [.one] := represented.2.2.2.2.1
  have header : (s 2).head? = some (literalTag literal) := by rw [wordReg]; exact encoded_head capacity literal rest
  refine ⟨?_, ?_, ?_⟩
  · have representedNext := inverseStep_represents (O := O) bit capacity active state s represented
    simpa only [state, NativeBody.step_literal bound literal valid rest seen enabled] using representedNext
  · simpa [inverseStep, Routine.branch, header, insideReg, literalTag_not_close, Routine.seq] using consumed
  · simpa [inverseStep, Routine.branch, header, insideReg, literalTag_not_close, Routine.seq] using transformed

theorem inverseStep_open {O : Type} (bit : Bool) (capacity active : ℕ) (rest : List Symbol)
    (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨.openClause :: rest, false, seen, enabled⟩ s) :
    let output := (inverseStep (O := O) bit).eval s
    Represents capacity active ⟨rest, true, false, enabled⟩ output ∧
      output 31 = s 31 ∧ output 21 = .openClause :: s 21 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa [NativeBody.step] using inverseStep_represents (O := O) bit capacity active _ s represented
  · have frame := bodyStep_upperFrame (O := O) s 31 (by decide) (by decide) (by decide)
    simp [inverseStep, Routine.branch, represented.1, represented.2.2.2.2.1,
      Routine.seq, Routine.ofLocal, Local.eval_push, frame]
  · have frame := bodyStep_upperFrame (O := O) s 21 (by decide) (by decide) (by decide)
    simp [inverseStep, Routine.branch, represented.1, represented.2.2.2.2.1,
      Routine.seq, Routine.ofLocal, Local.eval_push, frame]

theorem inverseStep_close {O : Type} (bit : Bool) (capacity active : ℕ) (rest : List Symbol)
    (seen enabled : Bool) (s : Store)
    (represented : Represents capacity active ⟨.closeClause :: rest, true, seen, enabled⟩ s) :
    let output := (inverseStep (O := O) bit).eval s
    Represents capacity active ⟨rest, false, false, enabled && seen⟩ output ∧
      output 31 = s 31 ∧ output 21 = .closeClause :: s 21 := by
  dsimp only
  refine ⟨?_, ?_, ?_⟩
  · simpa [NativeBody.step] using inverseStep_represents (O := O) bit capacity active _ s represented
  · have frame := bodyStep_upperFrame (O := O) s 31 (by decide) (by decide) (by decide)
    simp [inverseStep, Routine.branch, represented.1, represented.2.2.2.2.1,
      Routine.seq, Routine.ofLocal, Local.eval_push, frame]
  · have frame := bodyStep_upperFrame (O := O) s 21 (by decide) (by decide) (by decide)
    simp [inverseStep, Routine.branch, represented.1, represented.2.2.2.2.1,
      Routine.seq, Routine.ofLocal, Local.eval_push, frame]

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
