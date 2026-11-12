import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Components

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency false

def loadedStore (word label : List Symbol) : Store :=
  Function.update (Function.update (fun _ => []) 0 word.reverse) 1 label.reverse

def preparedStore (word label : List Symbol) : Store :=
  Function.update (Function.update (Function.update (fun _ => []) 2 word) 24 word) 25 label

theorem prepareInput_eval {O : Type} (word label : List Symbol) :
    (prepareInput (O := O)).eval (loadedStore word label) = preparedStore word label := by
  funext j
  fin_cases j <;> simp [prepareInput, loadedStore, preparedStore, Routine.seq, Routine.clearMany_eval,
    Routine.transfer, Routine.copy]

def savedStore {O : Type} (s : Store) : Store := (save (O := O)).eval ((parser (O := O)).eval s)

structure Saved (result source : Store) : Prop where
  raw : result 24 = source 24
  labelWord : result 25 = source 25
  sourceSize : (result 17).length = headerSize (source 2)
  startIndex : (result 26).length = (parsedState (source 2)).start
  sizeIndex : (result 27).length = headerSize (source 2)
  validity : result 16 = flag (wellFormed (source 2))

theorem saved_fields {O : Type} (s : Store) : Saved (savedStore (O := O) s) s := by
  have syntaxValue : acceptedSyntax ((parser (O := O)).eval s) = wellFormed (s 2) := parser_decides s
  constructor
  · simp [savedStore, save_eval, parser_eval, startEncoded, rowEncoded, cellEncoded, headerBase]
  · simp [savedStore, save_eval, parser_eval, startEncoded, rowEncoded, cellEncoded, headerBase]
  · simp [savedStore, save_eval, parser_eval, startEncoded, rowEncoded, cellEncoded]
  · simp [savedStore, save_eval, parser_eval, startEncoded]
  · simp [savedStore, save_eval, parser_eval, startEncoded, rowEncoded, cellEncoded]
  · simp only [savedStore, save_eval, Function.update_apply]
    change flag (acceptedSyntax ((parser (O := O)).eval s)) = flag (wellFormed (s 2))
    exact congrArg flag syntaxValue

theorem saved_graph {O : Type} (word label : List Symbol) (graph : Graph) (start : ℕ)
    (inside : start < graph.size) (encoded : graph.encode start = word) :
    Inputs (savedStore (O := O) (preparedStore word label)) graph start label ∧
      savedStore (O := O) (preparedStore word label) 16 = [Symbol.bit true] := by
  have fields := saved_fields (O := O) (preparedStore word label)
  have inputWord : preparedStore word label 2 = word := by simp [preparedStore]
  have raw : preparedStore word label 24 = graph.encode start := by simp [preparedStore, encoded]
  have inputLabel : preparedStore word label 25 = label := by simp [preparedStore]
  refine ⟨⟨fields.raw.trans raw, fields.labelWord.trans inputLabel, ?_, ?_, ?_⟩, ?_⟩
  · rw [fields.sourceSize, inputWord, ← encoded, headerSize_encode]
  · rw [fields.startIndex, inputWord, ← encoded, parsedState_encode graph start inside]
  · rw [fields.sizeIndex, inputWord, ← encoded, headerSize_encode]
  · rw [fields.validity, inputWord, ← encoded, wellFormed_encode graph start inside]
    rfl

theorem singleton_value {O : Type} (s : Store) :
    (singleton (O := O)).eval s 31 = if (s 25).isEmpty then s 24 else [] := by
  cases label : s 25 <;> simp [singleton, Routine.branch, Routine.clear, Routine.assign_eval, label]

end ComplexityOfGenerators.Examples.HAMPATH.Native.Reduction
