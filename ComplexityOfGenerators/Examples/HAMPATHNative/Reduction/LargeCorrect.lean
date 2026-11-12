import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Components

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

theorem Inputs.logarithm {O : Type} {s : Store} {graph : Graph} {start : ℕ} {label : List Symbol}
    (source : Inputs s graph start label) : Inputs ((Logarithm.routine (O := O)).eval s) graph start label := by
  apply source.of_frame
  intro i
  fin_cases i <;> exact Logarithm.routine_frame s _ (by decide) (by decide) (by decide)

theorem Inputs.labelBits {O : Type} {s : Store} {graph : Graph} {start : ℕ} {label : List Symbol}
    (source : Inputs s graph start label) : Inputs ((LabelBits.routine (O := O)).eval s) graph start label := by
  apply source.of_frame
  intro i
  fin_cases i <;> exact LabelBits.routine_frame s _ (by decide) (by decide) (by decide)

theorem Inputs.labelChecks {O : Type} {s : Store} {graph : Graph} {start : ℕ} {label : List Symbol}
    (source : Inputs s graph start label) : Inputs ((LabelChecks.routine (O := O)).eval s) graph start label := by
  apply source.of_frame
  intro i
  fin_cases i <;> exact LabelChecks.routine_frame s _ (by decide) (by decide) (by decide) (by decide) (by decide)

theorem large_value {O : Type} (s : Store) (graph : Graph) (start : ℕ) (label : List Symbol)
    (source : Inputs s graph start label) (valid : s 16 = [.bit true])
    (inside : start < graph.size) (big : 2 ≤ graph.size) :
    (large (O := O)).eval s 31 = wordReduce (graph.encode start) label := by
  let a := (Logarithm.routine (O := O)).eval s
  let b := (LabelBits.routine (O := O)).eval a
  let c := (LabelChecks.routine (O := O)).eval b
  let next := nextValue graph.size label
  have aSource : Inputs a graph start label := source.logarithm
  have bSource : Inputs b graph start label := aSource.labelBits
  have cSource : Inputs c graph start label := bSource.labelChecks
  have aWidth : (a 19).length = width graph.size := by
    have value := congrArg List.length (Logarithm.routine_value (O := O) s)
    simpa [a, source.sourceSize, width] using value
  have aValid : a 16 = [.bit true] :=
    (Logarithm.routine_frame (O := O) s 16 (by decide) (by decide) (by decide)).trans valid
  have bWidth : (b 19).length = width graph.size :=
    (congrArg List.length (LabelBits.routine_frame (O := O) a 19 (by decide) (by decide) (by decide))).trans aWidth
  have bNext : (b 28).length = next := by
    have value := congrArg List.length (LabelBits.routine_value (O := O) a)
    simpa only [List.length_replicate, aSource.labelWord, aWidth, nextValue, next] using value
  have bValid : b 16 = [.bit true] :=
    (LabelBits.routine_frame (O := O) a 16 (by decide) (by decide) (by decide)).trans aValid
  have cNext : (c 28).length = next :=
    (congrArg List.length (LabelChecks.routine_frame (O := O) b 28
      (by decide) (by decide) (by decide) (by decide) (by decide))).trans bNext
  have choice : LabelChecks.correct b = validCandidate graph.size start label := by
    simp only [LabelChecks.correct, validCandidate, bSource.labelWord, bWidth, bNext,
      bSource.sizeIndex, bSource.startIndex, next]
  have cValid : c 16 = if validCandidate graph.size start label then [Symbol.bit true] else [] := by
    have value := LabelChecks.routine_flag (O := O) b
    rw [choice, bValid] at value
    exact value
  change (afterLabel (O := O)).eval c 31 = _
  rw [afterLabel, Routine.guardedOutput_value, cValid, wordReduce_candidate graph start inside big label]
  cases good : validCandidate graph.size start label with
  | false => simp [candidate, good]
  | true =>
      have chosen : candidate graph.size start label = some next := by simp [candidate, good, next]
      have accepted := (candidate_some_iff graph.size start label next).mp chosen
      have nextBound := (decodeLabel_sound graph.size label next accepted.1).1
      let q := (Edge.query (O := O)).eval c
      have edgeValid : q 16 = if graph.edge start next then [Symbol.bit true] else [] := by
        have value := Edge.query_graph_flag (O := O) c graph start next inside nextBound
          cSource.raw cSource.startIndex cSource.sizeIndex cNext
        rw [cValid, good] at value
        simpa only [ite_true] using value
      have qWord : q 24 = graph.encode start :=
        (Edge.query_frame (O := O) c 24 (by decide)).trans cSource.raw
      have qRow : (q 26).length = start :=
        (congrArg List.length (Edge.query_frame (O := O) c 26 (by decide))).trans cSource.startIndex
      have qSize : (q 27).length = graph.size :=
        (congrArg List.length (Edge.query_frame (O := O) c 27 (by decide))).trans cSource.sizeIndex
      have qNext : (q 28).length = next :=
        (congrArg List.length (Edge.query_frame (O := O) c 28 (by decide))).trans cNext
      have deleted := Delete.routine_graph (O := O) q graph start next inside qWord qRow qSize qNext
      rw [chosen]
      simp only [good, List.head?_cons, Option.isSome_some, ite_true]
      change (afterEdge (O := O)).eval q 31 = _
      rw [afterEdge, Routine.guardedOutput_value, edgeValid]
      cases edge : graph.edge start next <;> simp [edge, deleted]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
