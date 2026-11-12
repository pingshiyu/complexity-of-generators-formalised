import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Basic

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def loaded (target label : List Symbol) : Memory :=
  ⟨(),0,0,[],Function.update (Function.update (fun _ => []) 0 target.reverse) 1 label.reverse⟩

def indexed (n : ℕ) (target label : List Symbol) : Memory :=
  Command.loadedIndex 34 (.bit true) n (loaded target label)

def preparedStore (n : ℕ) (target label : List Symbol) : Store :=
  Function.update (Function.update (Function.update (fun _ => []) 32 target) 33 label)
    34 (List.replicate n (.bit true))

def prepared (n : ℕ) (target label : List Symbol) : Memory :=
  ⟨(),n,0,[],preparedStore n target label⟩

theorem input_value (n : ℕ) (target label : List Symbol) :
    input.eval (indexed n target label).store=preparedStore n target label := by
  funext j
  fin_cases j <;> simp [input,indexed,loaded,preparedStore,Command.loadedIndex,Memory.set,
    Routine.seq,Routine.clearMany_eval,Routine.transfer]

noncomputable def classified (n : ℕ) (target label : List Symbol) : Memory :=
  {prepared n target label with store := Classify.routine.eval (preparedStore n target label)}

theorem classified_graph (graph : Graph) (start n : ℕ) (label : List Symbol) (inside : start<graph.size) :
    Classify.Result (classified n (graph.encode start) label).store graph start n label := by
  exact Classify.routine_graph (preparedStore n (graph.encode start) label) graph start n label inside
    (by simp [preparedStore]) (by simp [preparedStore]) (by simp [preparedStore])

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
