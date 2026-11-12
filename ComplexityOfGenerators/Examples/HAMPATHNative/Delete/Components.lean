import ComplexityOfGenerators.Examples.HAMPATHNative.MatrixErase.Graph
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel
import ComplexityOfGenerators.Simulation.WordStack.OneHot
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Delete

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def prefixWord (size : ℕ) : List Symbol := .separator :: List.replicate (size - 1) (.bit true)

def headerPrefix {O : Type} : Routine Symbol O 32 :=
  (Routine.clear 31).seq
    ((Routine.assign 27 29 9 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      ((Routine.ofLocal (Local.pop 29)).seq (Routine.ofLocal (Local.push 29 .separator))))

theorem headerPrefix_eval {O : Type} (s : Store) :
    (headerPrefix (O := O)).eval s = Function.update (Function.update (Function.update s
      31 []) 9 []) 29 (prefixWord (s 27).length) := by
  simp [headerPrefix, prefixWord, Routine.seq, Routine.clear, Routine.assign_eval, Routine.ofLocal,
    Local.eval, Local.pop, Local.push, Action.apply, List.map_const', List.tail_replicate]

def matrixSetup {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [3, 9, 10, 13, 30, 31]).seq
    ((Routine.assign 4 27 9 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      ((Routine.assign 26 7 9 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
        ((Routine.assign 7 26 9 (by decide) (by decide) (by decide) id).seq
          (Routine.ofLocal (Local.push 13 (.bit true))))))

theorem matrixSetup_eval {O : Type} (s : Store) :
    (matrixSetup (O := O)).eval s =
      MatrixErase.encoded s (s 4).length (s 26).length ⟨s 2, (s 26).length, true, s 29⟩ (s 5) := by
  funext j
  fin_cases j <;> simp [matrixSetup, MatrixErase.encoded, flag, Routine.seq, Routine.clearMany_eval,
    Routine.assign_eval, Routine.ofLocal, Local.eval, Local.push, Action.apply, List.map_const']

attribute [irreducible] matrixSetup

def matrixPrepare {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 24 2 9 (by decide) (by decide) (by decide) id).seq (header.seq matrixSetup)

def nextSlots : RationalSelection.Compare.Layout 32 := ⟨![26, 28, 20, 21, 22, 23], by decide⟩
def markSlots : OneHot.Layout 32 := ⟨![5, 3, 8, 29], by decide⟩

def contractPrepare {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 28 3 9 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
    ((RationalSelection.Compare.routine nextSlots (.bit true)).seq
      ((Routine.branch 20 fun below => if below.isSome then Routine.skip else Routine.ofLocal (Local.pop 3)).seq
        ((Routine.assign 27 5 9 (by decide) (by decide) (by decide) id).seq (Routine.ofLocal (Local.pop 5)))))

theorem contractPrepare_value {O : Type} (s : Store) :
    (contractPrepare (O := O)).eval s 3 = List.replicate (contract (s 26).length (s 28).length) (.bit true) ∧
    (contractPrepare (O := O)).eval s 5 = (s 27).tail ∧
    (contractPrepare (O := O)).eval s 29 = s 29 ∧
    (contractPrepare (O := O)).eval s 31 = s 31 := by
  by_cases below : (s 28).length < (s 26).length
  · have opposite : ¬ (s 26).length ≤ (s 28).length := by omega
    simp [contractPrepare, contract, Routine.seq, Routine.assign_eval, RationalSelection.Compare.routine_eval,
      nextSlots, Routine.branch, Routine.skip, Routine.ofLocal, Local.eval, Local.pop, Action.apply,
      below, opposite, List.map_const', List.tail_replicate]
  · have opposite : (s 26).length ≤ (s 28).length := by omega
    simp [contractPrepare, contract, Routine.seq, Routine.assign_eval, RationalSelection.Compare.routine_eval,
      nextSlots, Routine.branch, Routine.skip, Routine.ofLocal, Local.eval, Local.pop, Action.apply,
      below, opposite, List.map_const', List.tail_replicate]

attribute [irreducible] matrixPrepare contractPrepare

def finish {O : Type} : Routine Symbol O 32 :=
  (Routine.ofLocal (Local.push 29 Symbol.separator)).seq
    (contractPrepare.seq ((OneHot.routine markSlots Symbol.bit).seq (Routine.transfer 29 31 (by decide) id)))

def routine {O : Type} : Routine Symbol O 32 :=
  headerPrefix.seq (matrixPrepare.seq (MatrixErase.rows.seq finish))

end ComplexityOfGenerators.Examples.HAMPATH.Native.Delete
