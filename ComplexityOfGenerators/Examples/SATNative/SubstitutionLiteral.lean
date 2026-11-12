import ComplexityOfGenerators.Examples.SATNative.AssignmentBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack
open NativeAssignment

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 32

def equalitySlots : LengthTest.Layout 32 := ⟨![5, 10, 27, 22, 23, 9], by decide⟩

def replaceTag {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  Routine.branch 11 fun tag => match tag with
  | some .positive => Routine.branch 27 fun equal => if equal.isSome then
      (Routine.clear 5).seq (Routine.ofLocal (Local.write 11 (if bit then .trueConstant else .falseConstant)))
    else Routine.skip
  | some .negative => Routine.branch 27 fun equal => if equal.isSome then
      (Routine.clear 5).seq (Routine.ofLocal (Local.write 11 (if !bit then .trueConstant else .falseConstant)))
    else Routine.skip
  | _ => Routine.skip

/-- Native substitution changes only the last active variable. Its unary
index becomes zero and its tag becomes the chosen signed Boolean constant. -/
def rewriteLiteral {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  (LengthTest.routine equalitySlots .one).seq (replaceTag bit)

def metadata (base : Store) (active : ℕ) (literal : Literal) : Store :=
  Function.update (Function.update (Function.update base 10 (List.replicate active .one))
    5 (List.replicate (literalIndex literal) .one)) 11 [literalTag literal]

theorem rewriteLiteral_metadata {O : Type} (bit : Bool) (base : Store) (active : ℕ) (literal : Literal) :
    let output := (rewriteLiteral (O := O) bit).eval (metadata base active literal)
    output 5 = List.replicate (literalIndex (literal.substitute active bit)) .one ∧
      output 11 = [literalTag (literal.substitute active bit)] := by
  dsimp only
  cases literal with
  | constant value =>
    cases value <;> simp [rewriteLiteral, Routine.seq, LengthTest.routine_eval, equalitySlots,
      replaceTag, Routine.branch, Routine.skip, Routine.ofLocal, Local.eval, metadata,
      literalTag, literalIndex, Literal.substitute]
  | var index sign =>
    cases sign <;> by_cases fresh : index = active <;> cases bit <;>
      simp [rewriteLiteral, Routine.seq, LengthTest.routine_eval, equalitySlots,
        replaceTag, Routine.branch, Routine.skip, Routine.clear, Routine.ofLocal, Local.eval_write,
        metadata, literalTag, literalIndex, Literal.substitute, fresh]

def emitTag : Local Symbol 32 :=
  .read 11 fun tag => match tag with | none => .skip | some value => Local.push 21 value

theorem emitTag_eval (s : Store) : emitTag.eval s = Function.update s 21 ((s 11).head?.toList ++ s 21) := by
  cases head : (s 11).head? <;> simp [emitTag, Local.eval, Local.push, Action.apply, head, Function.update_eq_self]

/-- Append one reconstructed padded record to the reversed output buffer.
Every unary copy and subtraction is charged by its underlying finite routine. -/
def emitLiteral {O : Type} : Routine Symbol O 32 :=
  (Routine.ofLocal emitTag).seq
  ((Routine.copy 5 21 9 (by decide) (by decide) (by decide) (fun _ => .one)).seq
  ((Routine.assign 4 22 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.assign 5 23 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.clear 24).seq
  ((DrainPair.routine 23 22 24 (by decide) (by decide)).seq
    (Routine.transfer 22 21 (by decide) (fun _ => .zero)))))))

theorem emitLiteral_buffer {O : Type} (s : Store) :
    (emitLiteral (O := O)).eval s 21 =
      List.replicate ((s 4).length - (s 5).length) .zero ++
        List.replicate (s 5).length .one ++ (s 11).head?.toList ++ s 21 := by
  simp [emitLiteral, Routine.seq, Routine.ofLocal, emitTag_eval, Routine.copy, Routine.assign_eval,
    Routine.clear, DrainPair.routine_eval (23 : Fin 32) 22 24 (by decide) (by decide) (by decide),
    Routine.transfer, List.map_reverse, List.length_drop, List.append_assoc]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
