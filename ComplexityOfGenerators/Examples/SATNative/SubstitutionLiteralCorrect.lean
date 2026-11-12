import ComplexityOfGenerators.Examples.SATNative.SubstitutionLiteral

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeAssignment

set_option backward.isDefEq.respectTransparency false

theorem rewriteLiteral_frame {O : Type} (bit : Bool) (s : Store) (j : Fin 32)
    (index : j ≠ 5) (scratch : j ≠ 9) (tag : j ≠ 11) (copy : j ≠ 22)
    (counter : j ≠ 23) (flag : j ≠ 27) :
    (rewriteLiteral (O := O) bit).eval s j = s j := by
  cases head : (s 11).head? with
  | none => simp [rewriteLiteral, Routine.seq, LengthTest.routine_eval, equalitySlots,
      replaceTag, Routine.branch, Routine.skip, Routine.ofLocal, Local.eval,
      head, index, scratch, tag, copy, counter, flag]
  | some symbol =>
    cases symbol <;> by_cases same : (s 5).length = (s 10).length <;>
      simp [rewriteLiteral, Routine.seq, LengthTest.routine_eval, equalitySlots,
        replaceTag, Routine.branch, Routine.skip, Routine.clear, Routine.ofLocal, Local.eval_write,
        head, same, index, scratch, tag, copy, counter, flag]

theorem emitLiteral_frame {O : Type} (s : Store) (j : Fin 32)
    (scratch : j ≠ 9) (buffer : j ≠ 21) (copy : j ≠ 22) (counter : j ≠ 23) (discarded : j ≠ 24) :
    (emitLiteral (O := O)).eval s j = s j := by
  simp [emitLiteral, Routine.seq, Routine.ofLocal, emitTag_eval, Routine.copy, Routine.assign_eval,
    Routine.clear, DrainPair.routine_eval (23 : Fin 32) 22 24 (by decide) (by decide) (by decide),
    Routine.transfer, scratch, buffer, copy, counter, discarded]

def substituteLiteral {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  (rewriteLiteral bit).seq emitLiteral

theorem literal_record (capacity : ℕ) (literal : Literal) :
    literal.encode capacity = [literalTag literal] ++ List.replicate (literalIndex literal) .one ++
      List.replicate (capacity - literalIndex literal) .zero := by
  cases literal with
  | constant value => cases value <;> simp [Literal.encode, literalTag, literalIndex]
  | var index sign => cases sign <;> simp [Literal.encode, literalTag, literalIndex]

/-- The actual finite literal transformer emits precisely the padded record
for semantic substitution, appended to its reversed stream buffer. -/
theorem substituteLiteral_buffer {O : Type} (bit : Bool) (base : Store) (capacity active : ℕ) (literal : Literal)
    (cap : base 4 = List.replicate capacity .one) :
    (substituteLiteral (O := O) bit).eval (metadata base active literal) 21 =
      ((literal.substitute active bit).encode capacity).reverse ++ base 21 := by
  have fields := rewriteLiteral_metadata (O := O) bit base active literal
  dsimp only at fields
  have savedCap := rewriteLiteral_frame (O := O) bit (metadata base active literal) 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have savedBuffer := rewriteLiteral_frame (O := O) bit (metadata base active literal) 21
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  simp only [substituteLiteral, Routine.seq, emitLiteral_buffer, fields.1, fields.2,
    savedCap, savedBuffer]
  simp [metadata, cap, literal_record, List.reverse_append, List.append_assoc]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
