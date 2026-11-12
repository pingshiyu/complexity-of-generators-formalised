import ComplexityOfGenerators.Examples.SATNative.InverseNative.Literal
import ComplexityOfGenerators.Examples.SATNative.SubstitutionHeader

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

open Simulation.WordStack
open NativeSubstitution (Store headerWord)

set_option backward.isDefEq.respectTransparency false

/-- Rebuild the padded header with one newly active variable, while keeping
the original capacity and active-count registers for the inverse literal scan. -/
def emitHeader {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 21).seq
  ((Routine.copy 4 21 9 (by decide) (by decide) (by decide) (fun _ => .one)).seq
  ((Routine.ofLocal (Local.push 21 .separator)).seq
  ((Routine.assign 10 22 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.ofLocal (Local.push 22 .one)).seq
  ((Routine.copy 22 21 9 (by decide) (by decide) (by decide) (fun _ => .one)).seq
  ((Routine.assign 4 23 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.assign 22 24 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.clear 25).seq
  ((DrainPair.routine 24 23 25 (by decide) (by decide)).seq
  ((Routine.transfer 23 21 (by decide) (fun _ => .zero)).seq
    (Routine.ofLocal (Local.push 21 .separator))))))))))))

theorem emitHeader_buffer {O : Type} (s : Store) :
    (emitHeader (O := O)).eval s 21 = (headerWord (s 4).length ((s 10).length + 1)).reverse := by
  simp [emitHeader, Routine.seq, Routine.ofLocal, Routine.clear, Routine.copy, Routine.assign_eval,
    Local.eval_pop, Local.eval_push, DrainPair.routine_eval (24 : Fin 32) 23 25 (by decide) (by decide) (by decide),
    Routine.transfer, headerWord, List.map_reverse, List.reverse_append, List.length_tail, List.length_drop,
    List.append_assoc, List.replicate_succ]
  have same : Symbol.one :: List.replicate (s 10).length .one =
      List.replicate (s 10).length .one ++ [.one] := by
    rw [← List.replicate_succ, List.replicate_succ']
  simpa only [List.cons_append, List.append_assoc, List.singleton_append, List.nil_append] using
    congrArg (fun word => word ++ Symbol.separator :: List.replicate (s 4).length .one) same

theorem emitHeader_frame {O : Type} (s : Store) (j : Fin 32)
    (scratch : j ≠ 9) (buffer : j ≠ 21) (activeCopy : j ≠ 22) (capacityCopy : j ≠ 23)
    (counter : j ≠ 24) (discarded : j ≠ 25) :
    (emitHeader (O := O)).eval s j = s j := by
  simp [emitHeader, Routine.seq, Routine.ofLocal, Routine.clear, Routine.copy, Routine.assign_eval,
    Local.eval_pop, Local.eval_push, DrainPair.routine_eval (24 : Fin 32) 23 25 (by decide) (by decide) (by decide),
    Routine.transfer, scratch, buffer, activeCopy, capacityCopy, counter, discarded]

end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
