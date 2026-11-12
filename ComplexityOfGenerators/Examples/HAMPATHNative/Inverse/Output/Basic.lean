import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.MatrixInsert.Native
import ComplexityOfGenerators.Examples.HAMPATHNative.ParserModel
import ComplexityOfGenerators.Simulation.WordStack.OneHot

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Output

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

abbrev Store := Local.Store Symbol 64

def low16 : Fin 16 ↪ Fin 64 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b same := Fin.ext (congrArg (fun j : Fin 64 => j.val) same)

def low32 : Fin 32 ↪ Fin 64 where
  toFun j := ⟨j.val, by omega⟩
  inj' a b same := Fin.ext (congrArg (fun j : Fin 64 => j.val) same)

def newRowSlots : InsertAt.Layout 64 := ⟨![45,40,46,47,48], by decide⟩
def markSlots : OneHot.Layout 64 := ⟨![46,47,48,43], by decide⟩

/-- High registers hold the target word, child/parent sizes, insertion
position and incident-edge words. Low registers are owned workspace. -/
def headerPrefix {O : Type} : Routine Symbol O 64 :=
  (Routine.assign 37 43 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
    (Routine.ofLocal (Local.push 43 .separator))

def matrixSetup {O : Type} : Routine Symbol O 64 :=
  (Routine.clearMany [6,7,8,9,10,11,12,13,14]).seq
    ((Routine.assign 2 0 48 (by decide) (by decide) (by decide) id).seq
      ((Routine.assign 35 1 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
        ((Routine.assign 40 2 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
          ((Routine.assign 44 3 48 (by decide) (by decide) (by decide) id).seq
            ((Routine.assign 45 4 48 (by decide) (by decide) (by decide) id).seq
              (Routine.assign 43 5 48 (by decide) (by decide) (by decide) id))))))

noncomputable def matrixPrepare {O : Type} : Routine Symbol O 64 :=
  (Routine.assign 32 2 48 (by decide) (by decide) (by decide) id).seq
    (((header (O := O)).rename low32).seq matrixSetup)

def finish {O : Type} : Routine Symbol O 64 :=
  (Routine.assign 5 43 48 (by decide) (by decide) (by decide) id).seq
    ((Routine.ofLocal (Local.push 43 .separator)).seq
      ((Routine.assign 37 46 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
        ((Routine.assign 40 47 48 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
          ((OneHot.routine markSlots Symbol.bit).seq
            ((Routine.clear 31).seq (Routine.transfer 43 31 (by decide) id))))))

noncomputable def routine {O : Type} : Routine Symbol O 64 :=
  headerPrefix.seq
    ((InsertAt.routine newRowSlots (.bit true) (.bit false)).seq
      (matrixPrepare.seq (((MatrixInsert.routine (O := O)).rename low16).seq finish)))

theorem headerPrefix_eval {O : Type} (s : Store) :
    (headerPrefix (O := O)).eval s = Function.update (Function.update s 48 [])
      43 (.separator :: List.replicate (s 37).length (.bit true)) := by
  simp [headerPrefix,Routine.seq,Routine.assign_eval,Routine.ofLocal,Local.eval_push,List.map_const']

theorem matrixSetup_project {O : Type} (s : Store) :
    ((matrixSetup (O := O)).eval s) ∘ low16 =
      MatrixInsert.encoded (s ∘ low16) (s 35).length (s 40).length (s 45)
        ⟨s 2,s 44,s 43⟩ [] [] := by
  funext j
  fin_cases j <;> simp [matrixSetup,MatrixInsert.encoded,low16,Function.comp_def,
    Routine.seq,Routine.clearMany_eval,Routine.assign_eval,List.map_const']

theorem matrixSetup_frame {O : Type} (s : Store) (j : Fin 64) (outside : 16 ≤ j.val)
    (scratch : j ≠ 48) : (matrixSetup (O := O)).eval s j = s j := by
  have different (i : Fin 64) (inside : i.val < 16) : j ≠ i := by
    intro equal
    have := congrArg Fin.val equal
    omega
  simp [matrixSetup,Routine.seq,Routine.clearMany_eval,Routine.assign_eval,
    Function.update_apply,scratch,different]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Output
