import ComplexityOfGenerators.Examples.HAMPATHNative.Delete.Bounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Edge.Bounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Edge.Graph
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelBitsBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelChecksBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.LabelModel
import ComplexityOfGenerators.Examples.HAMPATHNative.LogarithmBounds
import ComplexityOfGenerators.Examples.HAMPATHNative.Metadata
import ComplexityOfGenerators.Simulation.WordStack.GuardedOutput

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def prepareInput {O : Type} : Routine Symbol O 32 :=
  (Routine.clearMany [2, 24, 25, 29, 31]).seq
    ((Routine.transfer 0 2 (by decide) id).seq
      ((Routine.copy 2 24 23 (by decide) (by decide) (by decide) id).seq (Routine.transfer 1 25 (by decide) id)))

def save {O : Type} : Routine Symbol O 32 :=
  metadata.seq
    ((Routine.assign 13 26 18 (by decide) (by decide) (by decide) (fun _ => .bit true)).seq
      (Routine.assign 4 27 18 (by decide) (by decide) (by decide) (fun _ => .bit true)))

theorem save_eval {O : Type} (s : Store) :
    (save (O := O)).eval s =
      Function.update (Function.update (Function.update (Function.update (Function.update s
        16 (flag (acceptedSyntax s))) 17 (List.replicate (s 4).length (.bit true))) 18 [])
        26 (List.replicate (s 13).length (.bit true))) 27 (List.replicate (s 4).length (.bit true)) := by
  funext j
  by_cases valid : j = 16 <;> by_cases source : j = 17 <;> by_cases scratch : j = 18 <;>
    by_cases row : j = 26 <;> by_cases size : j = 27 <;>
      simp [save, Routine.seq, metadata_eval, Routine.assign_eval, Function.update_apply,
        valid, source, scratch, row, size, List.map_const']

def afterEdge {O : Type} : Routine Symbol O 32 := Routine.guardedOutput 16 31 Delete.routine
def edgeAndDelete {O : Type} : Routine Symbol O 32 := Edge.query.seq afterEdge
def afterLabel {O : Type} : Routine Symbol O 32 := Routine.guardedOutput 16 31 edgeAndDelete

noncomputable def large {O : Type} : Routine Symbol O 32 :=
  Logarithm.routine.seq (LabelBits.routine.seq (LabelChecks.routine.seq afterLabel))

def singleton {O : Type} : Routine Symbol O 32 :=
  Routine.branch 25 fun label => if label.isSome then Routine.clear 31
    else Routine.assign 24 31 18 (by decide) (by decide) (by decide) id

noncomputable def chooseSize {O : Type} : Routine Symbol O 32 :=
  (Routine.assign 27 21 18 (by decide) (by decide) (by decide) id).seq
    ((Routine.ofLocal (Local.pop 21)).seq
      (Routine.branch 21 fun size => if size.isSome then large else singleton))

noncomputable def dispatch {O : Type} : Routine Symbol O 32 := Routine.guardedOutput 16 31 chooseSize

noncomputable def routine {O : Type} : Routine Symbol O 32 := prepareInput.seq (parser.seq (save.seq dispatch))

structure Inputs (s : Store) (graph : Graph) (start : ℕ) (label : List Symbol) : Prop where
  raw : s 24 = graph.encode start
  labelWord : s 25 = label
  sourceSize : (s 17).length = graph.size
  startIndex : (s 26).length = start
  sizeIndex : (s 27).length = graph.size

def protectedRegisters : Fin 5 → Fin 32 := ![24, 25, 17, 26, 27]

theorem Inputs.of_frame {s t : Store} {graph : Graph} {start : ℕ} {label : List Symbol}
    (source : Inputs s graph start label)
    (frame : ∀ i : Fin 5, t (protectedRegisters i) = s (protectedRegisters i)) : Inputs t graph start label where
  raw := (frame 0).trans source.raw
  labelWord := (frame 1).trans source.labelWord
  sourceSize := (congrArg List.length (frame 2)).trans source.sourceSize
  startIndex := (congrArg List.length (frame 3)).trans source.startIndex
  sizeIndex := (congrArg List.length (frame 4)).trans source.sizeIndex

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
