import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Finish
import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.ValueControl

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 2000

theorem enabled_inputs (s : Store) (graph : Graph) (start n : ℕ) (word : List Symbol)
    (result : Classify.Result s graph start n word) (nonempty : word≠[])
    (live : (s 41).head?.isSome=true) :
    BaseSearch.Productive n ∧ encodingLength (graph.size+1)≤n ∧
      ∃ next, decodeLabel (graph.size+1) word=some next ∧
        s 39=List.replicate next (.bit true) := by
  have enabled : Classify.enabled n graph.size word=true := result.live.symm.trans live
  have facts : BaseSearch.Productive n ∧ encodingLength (graph.size+1)≤n ∧
      (decodeLabel (graph.size+1) word).isSome=true := by
    simpa [Classify.enabled,List.isEmpty_iff,nonempty,Bool.and_eq_true,and_assoc] using enabled
  refine ⟨facts.1,facts.2.1,?_⟩
  cases decoded : decodeLabel (graph.size+1) word with
  | none => simp [decoded] at facts
  | some next =>
      refine ⟨next,rfl,?_⟩
      rw [result.next nonempty,nextValue_of_decodeLabel _ _ _ decoded]

theorem chosen_fields (s : Store) (graph : Graph) (start n next : ℕ) (word : List Symbol)
    (result : Classify.Result s graph start n word) (nonempty : word≠[])
    (decoded : decodeLabel (graph.size+1) word=some next) (bits : List Bool)
    (sourceBits : s 42=bits.map Symbol.bit) (inside : start<graph.size)
    (enough : width (graph.size+1)+2*graph.size≤bits.length) :
    Choose.Result (Choose.routine.eval s) s graph.size start next (width (graph.size+1)) bits := by
  apply Choose.routine_values s graph.size start next (width (graph.size+1)) bits
  · simp [result.childSize]
  · simp [result.childStart]
  · rw [result.next nonempty,nextValue_of_decodeLabel _ _ _ decoded]
    simp
  · simp [result.labelWidth]
  · exact sourceBits
  · exact inside
  · exact enough

theorem chosen_output (s : Store) (graph : Graph) (start n next position : ℕ) (word : List Symbol)
    (result : Classify.Result s graph start n word) (nonempty : word≠[])
    (decoded : decodeLabel (graph.size+1) word=some next) (bits : List Bool)
    (sourceBits : s 42=bits.map Symbol.bit) (inside : start<graph.size)
    (enough : width (graph.size+1)+2*graph.size≤bits.length)
    (selected : Position.value graph.size start next
      (FixedBitBlocks.decode (bits.take (width (graph.size+1))))=some position) :
    (Output.routine (O := Symbol)).eval (Choose.routine.eval s) 31 =
      (graph.insert position
        (rowFromBits ((bits.drop (width (graph.size+1))).take graph.size))
        (forcedRow ((bits.drop (width (graph.size+1)+graph.size)).take graph.size) start)).encode position ∧
      Choose.routine.eval s 41=s 41 := by
  have fields := chosen_fields s graph start n next word result nonempty decoded bits sourceBits inside enough
  have positionBound := (Position.value_sound graph.size start next _ position inside selected).1
  have inputLength : ((bits.drop (width (graph.size+1))).take graph.size).length=graph.size := by
    simp only [List.length_take,List.length_drop]
    omega
  have canonicalIncoming :
      (List.range graph.size).map (fun vertex => Symbol.bit
        (rowFromBits ((bits.drop (width (graph.size+1))).take graph.size) vertex)) =
      ((bits.drop (width (graph.size+1))).take graph.size).map Symbol.bit := by
    have value := Choose.rowFromBits_word ((bits.drop (width (graph.size+1))).take graph.size)
    simpa only [inputLength] using value
  constructor
  · apply Output.routine_graph (O := Symbol) (Choose.routine.eval s) graph start position
    · exact (Choose.routine_frame s 0).trans result.raw
    · have frame : Choose.routine.eval s 35=s 35 := Choose.routine_frame s 3
      rw [frame,result.childSize]
      simp
    · have frame : Choose.routine.eval s 37=s 37 := Choose.routine_frame s 5
      rw [frame,result.parentSize]
      simp
    · rw [fields.chosen,selected]
      simp
    · exact positionBound
    · exact fields.incoming.trans canonicalIncoming.symm
    · exact fields.outgoing
  · rw [fields.live,selected]
    rfl

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
