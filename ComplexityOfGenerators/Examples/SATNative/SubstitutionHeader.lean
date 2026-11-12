import ComplexityOfGenerators.Examples.SATNative.SubstitutionLiteralCorrect

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def headerWord (capacity active : ℕ) : List Symbol :=
  List.replicate capacity .one ++ [.separator] ++ List.replicate active .one ++
    List.replicate (capacity - active) .zero ++ [.separator]

/-- Rebuild the fixed-width header with active count d-1, retaining capacity
and active-count registers for subsequent literal substitutions. -/
def emitHeader {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 21).seq
  ((Routine.copy 4 21 9 (by decide) (by decide) (by decide) (fun _ => .one)).seq
  ((Routine.ofLocal (Local.push 21 .separator)).seq
  ((Routine.assign 10 22 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.ofLocal (Local.pop 22)).seq
  ((Routine.copy 22 21 9 (by decide) (by decide) (by decide) (fun _ => .one)).seq
  ((Routine.assign 4 23 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.assign 22 24 9 (by decide) (by decide) (by decide) id).seq
  ((Routine.clear 25).seq
  ((DrainPair.routine 24 23 25 (by decide) (by decide)).seq
  ((Routine.transfer 23 21 (by decide) (fun _ => .zero)).seq
    (Routine.ofLocal (Local.push 21 .separator))))))))))))

theorem emitHeader_buffer {O : Type} (s : Store) :
    (emitHeader (O := O)).eval s 21 = (headerWord (s 4).length ((s 10).length - 1)).reverse := by
  simp [emitHeader, Routine.seq, Routine.ofLocal, Routine.clear, Routine.copy, Routine.assign_eval,
    Local.eval_pop, Local.eval_push, DrainPair.routine_eval (24 : Fin 32) 23 25 (by decide) (by decide) (by decide),
    Routine.transfer, headerWord, List.map_reverse, List.reverse_append, List.length_tail, List.length_drop,
    List.append_assoc]

theorem emitHeader_frame {O : Type} (s : Store) (j : Fin 32)
    (scratch : j ≠ 9) (buffer : j ≠ 21) (activeCopy : j ≠ 22) (capacityCopy : j ≠ 23)
    (counter : j ≠ 24) (discarded : j ≠ 25) :
    (emitHeader (O := O)).eval s j = s j := by
  simp [emitHeader, Routine.seq, Routine.ofLocal, Routine.clear, Routine.copy, Routine.assign_eval,
    Local.eval_pop, Local.eval_push, DrainPair.routine_eval (24 : Fin 32) 23 25 (by decide) (by decide) (by decide),
    Routine.transfer, scratch, buffer, activeCopy, capacityCopy, counter, discarded]

end ComplexityOfGenerators.Examples.PaddedCNF.NativeSubstitution
