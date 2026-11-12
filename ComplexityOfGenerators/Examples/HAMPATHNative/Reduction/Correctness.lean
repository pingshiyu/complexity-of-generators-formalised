import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.LargeCorrect
import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Views

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem chooseSize_value {O : Type} (s : Store) (graph : Graph) (start : ℕ) (label : List Symbol)
    (source : Inputs s graph start label) (valid : s 16 = [Symbol.bit true]) (inside : start < graph.size) :
    (chooseSize (O := O)).eval s 31 = wordReduce (graph.encode start) label := by
  let a := (Routine.assign (O := O) 27 21 18 (by decide) (by decide) (by decide) id).eval s
  let b := (Routine.ofLocal (O := O) (Local.pop (21 : Fin 32))).eval a
  have bSource : Inputs b graph start label := by
    apply source.of_frame
    intro i
    fin_cases i <;> simp [b, a, protectedRegisters, Routine.assign_eval, Routine.ofLocal, Local.eval_pop]
  have bValid : b 16 = [Symbol.bit true] := by
    simpa [b, a, Routine.assign_eval, Routine.ofLocal, Local.eval_pop] using valid
  have count : (b 21).length = graph.size - 1 := by
    simp [b, a, Routine.assign_eval, Routine.ofLocal, Local.eval_pop, List.length_tail, source.sizeIndex]
  have head : (b 21).head?.isSome = decide (0 < graph.size - 1) := by
    simpa only [List.drop_zero, count] using RationalSelection.Compare.remaining_nonempty (b 21) 0
  change (Routine.branch (S := Symbol) (O := O) 21 fun size => if size.isSome then large else singleton).eval b 31 = _
  by_cases big : 2 ≤ graph.size
  · have positive : 0 < graph.size - 1 := by omega
    simp only [Routine.branch, head, positive, decide_true, ite_true]
    exact large_value b graph start label bSource bValid inside big
  · have sizeOne : graph.size = 1 := by omega
    simp only [Routine.branch, head, sizeOne, Nat.sub_self, Nat.lt_irrefl, decide_false, Bool.false_eq_true, ite_false]
    rw [singleton_value, bSource.labelWord, bSource.raw]
    cases label <;> simp [wordReduce, decode_encode graph start inside, sizeOne]

theorem routine_value {O : Type} (word label : List Symbol) :
    (routine (O := O)).eval (loadedStore word label) 31 = wordReduce word label := by
  let s := savedStore (O := O) (preparedStore word label)
  have fields := saved_fields (O := O) (preparedStore word label)
  have wordField : preparedStore word label 2 = word := by simp [preparedStore]
  have validity : s 16 = flag (wellFormed word) := by simpa only [wordField] using fields.validity
  simp only [routine, Routine.seq, prepareInput_eval]
  change (dispatch (O := O)).eval s 31 = _
  rw [dispatch, Routine.guardedOutput_value, validity]
  cases good : wellFormed word with
  | false =>
      have decoded : decode word = none := by
        cases found : decode word with
        | none => rfl
        | some value => have validWord := (wellFormed_iff_decode word).mpr (by simp [found]); rw [good] at validWord; cases validWord
      simp [good, flag, wordReduce, decoded]
  | true =>
      obtain ⟨graph, start, inside, encoded⟩ :=
        (decode_isSome_iff_encoding word).mp ((wellFormed_iff_decode word).mp good)
      obtain ⟨source, valid⟩ := saved_graph (O := O) word label graph start inside encoded
      have computed := chooseSize_value (O := O) s graph start label source valid inside
      simp only [good, flag, ite_true, List.head?_cons, Option.isSome_some]
      simpa only [encoded] using computed

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
