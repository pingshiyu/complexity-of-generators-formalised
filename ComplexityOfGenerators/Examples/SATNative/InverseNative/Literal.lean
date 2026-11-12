import ComplexityOfGenerators.Examples.SATNative.SubstitutionLiteralCorrect
import ComplexityOfGenerators.Examples.SATNative.InverseNative.Choices
import ComplexityOfGenerators.Simulation.WordStack.RoutineFrame

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack
open NativeAssignment (literalIndex literalTag)
open NativeSubstitution

set_option backward.isDefEq.respectTransparency false

def freshLiteral {O : Type} (value bit : Bool) : Routine Symbol O 32 :=
  (Routine.assign 10 5 9 (by decide) (by decide) (by decide) id).seq
    ((Routine.ofLocal (Local.push 5 .one)).seq
      (Routine.ofLocal (Local.write 11 (if value == bit then .positive else .negative))))

/-- The mask chooses independently at every literal. An old variable is
retained; a chosen constant becomes the newly active variable with its unique
sign evaluating to that constant. -/
def rewriteLiteral {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  Routine.branch 31 fun choice => if choice = some .one then
    Routine.branch 11 fun tag => match tag with
    | some .trueConstant => freshLiteral true bit
    | some .falseConstant => freshLiteral false bit
    | _ => Routine.skip
  else Routine.skip

theorem rewriteLiteral_frame {O : Type} (bit : Bool) (s : Store) (j : Fin 32)
    (index : j ≠ 5) (scratch : j ≠ 9) (tag : j ≠ 11) :
    (rewriteLiteral (O := O) bit).eval s j = s j := by
  by_cases choose : (s 31).head? = some .one
  · cases head : (s 11).head? with
    | none => simp [rewriteLiteral, Routine.branch, choose, head, Routine.skip, Routine.ofLocal, Local.eval]
    | some symbol => cases symbol <;>
        simp [rewriteLiteral, Routine.branch, choose, head, freshLiteral, Routine.seq,
          Routine.assign_eval, Routine.ofLocal, Local.eval, Routine.skip, Local.push, Local.write,
          Action.apply, index, scratch, tag]
  · simp [rewriteLiteral, Routine.branch, choose, Routine.skip, Routine.ofLocal, Local.eval]

theorem rewriteLiteral_metadata {O : Type} (bit : Bool) (base : Store) (active : ℕ)
    (literal : Literal) (choices : List Bool) (mask : base 31 = choices.map bitSymbol) :
    let out := (rewriteLiteral (O := O) bit).eval (metadata base active literal)
    out 5 = List.replicate (literalIndex (literal.lift active bit (choices.headD false))) .one ∧
      out 11 = [literalTag (literal.lift active bit (choices.headD false))] := by
  dsimp only
  cases choices with
  | nil => cases literal with
    | constant value => cases value <;>
        simp [rewriteLiteral, Routine.branch, metadata, mask, Routine.skip, Routine.ofLocal,
          Local.eval, Literal.lift, literalIndex, literalTag]
    | var index sign => cases sign <;>
        simp [rewriteLiteral, Routine.branch, metadata, mask, Routine.skip, Routine.ofLocal,
          Local.eval, Literal.lift, literalIndex, literalTag]
  | cons choice rest =>
      cases choice <;> cases literal with
      | constant value => cases value <;> cases bit <;>
          simp [rewriteLiteral, Routine.branch, metadata, mask, bitSymbol, freshLiteral, Routine.seq,
            Routine.assign_eval, Routine.ofLocal, Routine.skip, Local.eval_push, Local.eval_write,
            Local.eval, Literal.lift, literalIndex, literalTag, List.replicate_succ]
      | var index sign => cases sign <;>
          simp [rewriteLiteral, Routine.branch, metadata, mask, bitSymbol, Routine.skip, Routine.ofLocal,
            Local.eval, Literal.lift, literalIndex, literalTag]

def liftLiteral {O : Type} (bit : Bool) : Routine Symbol O 32 :=
  (rewriteLiteral bit).seq (emitLiteral.seq (Routine.ofLocal (Local.pop 31)))

theorem liftLiteral_frame {O : Type} (bit : Bool) (s : Store) (j : Fin 32)
    (index : j ≠ 5) (scratch : j ≠ 9) (tag : j ≠ 11) (buffer : j ≠ 21)
    (copy : j ≠ 22) (counter : j ≠ 23) (discarded : j ≠ 24) (mask : j ≠ 31) :
    (liftLiteral (O := O) bit).eval s j = s j := by
  change (Routine.ofLocal (O := O) (Local.pop 31)).eval
    ((emitLiteral (O := O)).eval ((rewriteLiteral (O := O) bit).eval s)) j = _
  simp only [Routine.ofLocal, Local.eval_pop, Function.update_of_ne mask]
  rw [emitLiteral_frame _ _ scratch buffer copy counter discarded,
    rewriteLiteral_frame bit s j index scratch tag]

theorem liftLiteral_mask {O : Type} (bit : Bool) (s : Store) :
    (liftLiteral (O := O) bit).eval s 31 = (s 31).tail := by
  simp only [liftLiteral, Routine.seq, Routine.ofLocal, Local.eval_pop, Function.update_self]
  rw [emitLiteral_frame _ _ (by decide) (by decide) (by decide) (by decide) (by decide),
    rewriteLiteral_frame _ _ _ (by decide) (by decide) (by decide)]

theorem liftLiteral_buffer {O : Type} (bit : Bool) (base : Store) (capacity active : ℕ)
    (literal : Literal) (choices : List Bool) (mask : base 31 = choices.map bitSymbol)
    (cap : base 4 = List.replicate capacity .one) :
    (liftLiteral (O := O) bit).eval (metadata base active literal) 21 =
      ((literal.lift active bit (choices.headD false)).encode capacity).reverse ++ base 21 := by
  have fields := rewriteLiteral_metadata (O := O) bit base active literal choices mask
  dsimp only at fields
  have savedCap := rewriteLiteral_frame (O := O) bit (metadata base active literal) 4 (by decide) (by decide) (by decide)
  have savedBuffer := rewriteLiteral_frame (O := O) bit (metadata base active literal) 21 (by decide) (by decide) (by decide)
  simp only [liftLiteral, Routine.seq, Routine.ofLocal, Local.eval_pop,
    Function.update_of_ne (show (21 : Fin 32) ≠ 31 by decide), emitLiteral_buffer,
    fields.1, fields.2, savedCap, savedBuffer]
  simp [metadata, cap, NativeSubstitution.literal_record, List.reverse_append, List.append_assoc]

theorem liftLiteral_buffer_of_fields {O : Type} (bit : Bool) (s : Store) (capacity active : ℕ)
    (literal : Literal) (choices : List Bool) (mask : s 31 = choices.map bitSymbol)
    (cap : s 4 = List.replicate capacity .one) (count : s 10 = List.replicate active .one)
    (index : s 5 = List.replicate (literalIndex literal) .one) (tag : s 11 = [literalTag literal]) :
    (liftLiteral (O := O) bit).eval s 21 =
      ((literal.lift active bit (choices.headD false)).encode capacity).reverse ++ s 21 := by
  have canonical : metadata s active literal = s := by
    simp only [metadata, ← count, ← index, ← tag, Function.update_eq_self]
  have result := liftLiteral_buffer (O := O) bit s capacity active literal choices mask cap
  simpa only [canonical] using result

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
