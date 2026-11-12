import ComplexityOfGenerators.Examples.SATNative.SubstitutionLiteralCorrect
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
open Simulation.WordStack NativeBody
set_option backward.isDefEq.respectTransparency false

private theorem clearWrite_bound {O : Type} (value : Symbol) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) :
    stackBound budget (((Routine.clear 5).seq (Routine.ofLocal (Local.write 11 value)) : Routine Symbol O 32).eval s) := by
  change StoreBound (((Routine.clear 5).seq (Routine.ofLocal (Local.write 11 value)) : Routine Symbol O 32).eval s) budget
  simp only [Routine.seq, Routine.clear, Routine.ofLocal, Local.eval_write]
  apply (StoreBound.clear sizes 5).update 11
  have tag := sizes 11
  simp only [Function.update_of_ne (by decide : (11 : Fin 32) ≠ 5), List.length_cons, List.length_tail]
  omega

theorem replaceTag_bound {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) :
    stackBound budget ((replaceTag (O := O) bit).eval s) := by
  cases tag : (s 11).head? with
  | none => simpa [replaceTag, Routine.branch, tag, Routine.skip, Routine.ofLocal, Local.eval] using sizes
  | some symbol =>
    cases symbol <;> simp only [replaceTag, Routine.branch, tag]
    all_goals first
      | exact sizes
      | split_ifs <;> first | exact sizes | exact clearWrite_bound _ s budget positive sizes

theorem replaceTag_cost {O : Type} (bit : Bool) (s : Store) (budget : ℕ) (sizes : stackBound budget s) :
    (replaceTag (O := O) bit).cost s ≤ 3*budget+6 := by
  have index := sizes 5
  cases tag : (s 11).head? with
  | none => simp [replaceTag, Routine.branch, tag, Routine.skip, Routine.ofLocal, Local.ticks]
  | some symbol =>
    cases symbol <;> cases pending : s 27 <;>
      simp [replaceTag, Routine.branch, tag, pending, Routine.skip, Routine.seq, Routine.clear,
        Routine.ofLocal, Local.write, Local.pop, Local.push, Local.ticks] <;> omega

theorem rewriteLiteral_bound {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) :
    stackBound budget ((rewriteLiteral (O := O) bit).eval s) := by
  have first : StoreBound ((LengthTest.routine (O := O) equalitySlots .one).eval s) budget :=
    StoreBound.lengthTest sizes equalitySlots .one (by omega)
  exact replaceTag_bound bit _ budget positive first

theorem rewriteLiteral_cost {O : Type} (bit : Bool) (s : Store) (budget : ℕ)
    (positive : 0 < budget) (sizes : stackBound budget s) :
    (rewriteLiteral (O := O) bit).cost s ≤ 90*(budget+1) := by
  have first := LengthTest.routine_cost (O := O) equalitySlots .one s budget sizes
  have after : StoreBound ((LengthTest.routine (O := O) equalitySlots .one).eval s) budget :=
    StoreBound.lengthTest sizes equalitySlots .one (by omega)
  have last := replaceTag_cost (O := O) bit _ budget after
  change (LengthTest.routine equalitySlots .one).cost s+1+
    (replaceTag bit).cost ((LengthTest.routine equalitySlots .one).eval s) ≤ _
  omega

theorem rewriteLiteral_index_length {O : Type} (bit : Bool) (s : Store) :
    ((rewriteLiteral (O := O) bit).eval s 5).length ≤ (s 5).length := by
  cases tag : (s 11).head? with
  | none => simp [rewriteLiteral, Routine.seq, LengthTest.routine_eval, equalitySlots, replaceTag, Routine.branch, tag, Routine.skip, Routine.ofLocal, Local.eval]
  | some symbol =>
    cases symbol <;> by_cases same : (s 5).length = (s 10).length <;>
      simp [rewriteLiteral, Routine.seq, LengthTest.routine_eval, equalitySlots, replaceTag, Routine.branch, tag,
        same, Routine.clear, Routine.ofLocal, Local.eval_write, Routine.skip, Local.eval]

/-- A padded record adds at most capacity+1 symbols, including malformed
empty tags, provided the index lies in the allocated capacity. -/
theorem emitLiteral_length {O : Type} (s : Store) (within : (s 5).length ≤ (s 4).length) :
    ((emitLiteral (O := O)).eval s 21).length ≤ (s 21).length+(s 4).length+1 := by
  rw [emitLiteral_buffer]
  have head : (s 11).head?.toList.length ≤ 1 := by cases (s 11).head? <;> simp
  simp only [List.length_append, List.length_replicate]
  omega

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
