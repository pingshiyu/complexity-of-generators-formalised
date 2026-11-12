import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Choose.Basic
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Value

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem insert_erase_eq_set (word : List Symbol) (position : ℕ) (inside : position < word.length)
    (letter : Symbol) :
    InsertAt.insertAt (word.eraseIdx position) position letter = word.set position letter := by
  induction word generalizing position with
  | nil => simp at inside
  | cons head rest ih =>
      cases position with
      | zero => simp [InsertAt.insertAt]
      | succ position =>
          simpa [InsertAt.insertAt] using congrArg (head :: ·)
            (ih position (by simp only [List.length_cons] at inside; omega))

theorem rowFromBits_word (bits : List Bool) :
    (List.range bits.length).map (fun vertex => Symbol.bit (rowFromBits bits vertex)) = bits.map Symbol.bit := by
  apply List.ext_getElem
  · simp
  · intro index left right
    have inside : index < bits.length := by simpa using right
    simp [List.getElem_map,List.getElem_range,rowFromBits,List.getElem?_eq_getElem inside]

theorem forcedRow_word (bits : List Bool) (start : ℕ) (inside : start < bits.length) :
    (bits.map Symbol.bit).set start (.bit true) =
      (List.range bits.length).map (fun vertex => Symbol.bit (forcedRow bits start vertex)) := by
  apply List.ext_getElem
  · simp
  · intro index left right
    have indexBound : index < bits.length := by simpa using right
    by_cases same : index=start
    · subst index
      simp [List.getElem_set,forcedRow]
    · simp [List.getElem_set,forcedRow,same,Ne.symm same,rowFromBits,List.getElem?_eq_getElem indexBound]

theorem forceEdge_eval (s : Store) :
    forceEdge.eval s = Function.update (Function.update (Function.update (Function.update s
      48 []) 47 []) 46 []) 45
        (InsertAt.insertAt ((s 45).eraseIdx (s 36).length) (s 36).length (.bit true)) := by
  funext j
  by_cases word : j=45 <;> by_cases first : j=46 <;> by_cases second : j=47 <;> by_cases scratch : j=48 <;>
    simp [forceEdge,Routine.seq,DropAt.routine_eval,InsertAt.routine_eval,forceSlots,
      Function.update_apply,word,first,second,scratch]

theorem forceEdge_word (s : Store) (bits : List Bool) (start : ℕ)
    (word : s 45=bits.map Symbol.bit) (position : (s 36).length=start) (inside : start<bits.length) :
    forceEdge.eval s 45 =
      (List.range bits.length).map (fun vertex => Symbol.bit (forcedRow bits start vertex)) := by
  rw [forceEdge_eval]
  simp only [Function.update_self,word,position]
  rw [insert_erase_eq_set _ start (by simpa using inside),forcedRow_word bits start inside]

theorem forceEdge_frame (s : Store) (j : Fin 64) (word : j≠45)
    (first : j≠46) (second : j≠47) (scratch : j≠48) : forceEdge.eval s j=s j := by
  simp [forceEdge_eval,word,first,second,scratch]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Choose
