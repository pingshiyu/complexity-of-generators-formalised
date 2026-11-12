import ComplexityOfGenerators.Examples.SATNative.LiteralModel
import ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare

namespace ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral

open Simulation.WordStack
open NativeHeader

set_option backward.isDefEq.respectTransparency false

def inputStore (base : Store) (capacity active : ℕ) (word : List Symbol) (enabled : Bool) : Store :=
  Function.update (Function.update (Function.update (Function.update base 2 word)
    4 (List.replicate capacity .one)) 10 (List.replicate active .one)) 6 (if enabled then [.one] else [])

def scaffold (base : Store) (capacity active : ℕ) (word : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (Function.update
    (Function.update (Function.update (Function.update base
      4 (List.replicate capacity .one)) 10 (List.replicate active .one)) 11 word.head?.toList)
      9 []) 12 []) 13 []) 14 []) 15 []

def tagCode : Local Symbol 16 :=
  .read 2 fun tag => match tag with
  | none => Local.pop 2
  | some symbol => (Local.push 11 symbol).seq (Local.pop 2)

def setup {O : Type} : Routine Symbol O 16 :=
  (Routine.clearMany [5, 7, 8, 9, 11, 12, 13, 14, 15]).seq
    ((Routine.ofLocal (Local.push 8 .one)).seq
      ((Routine.ofLocal tagCode).seq NativeHeader.clockSetup))

theorem setup_eval {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol) (enabled : Bool) :
    (setup (O := O)).eval (inputStore base capacity active word enabled) =
      NativeHeader.encoded (scaffold base capacity active word)
        ⟨word.tail, 0, true, enabled⟩ (List.replicate capacity .one) := by
  cases word with
  | nil =>
    cases enabled <;> funext j <;> fin_cases j <;>
      simp [setup, Routine.seq, Routine.clearMany_eval, Routine.ofLocal, NativeHeader.clockSetup,
        Routine.assign_eval, inputStore, scaffold, tagCode, Local.eval, Local.push, Local.pop, Action.apply,
        NativeHeader.encoded]
  | cons head rest =>
    cases enabled <;> funext j <;> fin_cases j <;>
      simp [setup, Routine.seq, Routine.clearMany_eval, Routine.ofLocal, NativeHeader.clockSetup,
        Routine.assign_eval, inputStore, scaffold, tagCode, Local.eval, Local.push, Local.pop, Action.apply,
        NativeHeader.encoded]

def indexSlots : RationalSelection.Compare.Layout 16 := ⟨![15, 5, 12, 13, 14, 9], by decide⟩

def indexSetup {O : Type} : Routine Symbol O 16 :=
  (Routine.assign 10 15 9 (by decide) (by decide) (by decide) id).seq
    (Routine.ofLocal (Local.push 15 .one))

def indexRoutine {O : Type} : Routine Symbol O 16 :=
  indexSetup.seq (RationalSelection.Compare.routine indexSlots .one)

def tagCheck : Local Symbol 16 :=
  .read 11 fun tag => match tag with
  | some .trueConstant | some .falseConstant =>
      .read 5 fun index => if index.isSome then Local.pop 6 else .skip
  | some .positive | some .negative =>
      .read 5 fun index => if index.isSome then
        Local.read 12 fun within => if within.isSome then .skip else Local.pop 6
      else Local.pop 6
  | _ => Local.pop 6

/-- The native syntax checker for one M+1-symbol padded literal record.
Capacity is in register4; the saved active-variable count is in register10.
It leaves the tag in11, unary literal index in5, and cumulative validity in6. -/
def literalRoutine {O : Type} : Routine Symbol O 16 :=
  setup.seq (NativeHeader.scanRoutine.seq (indexRoutine.seq (Routine.ofLocal tagCheck)))

theorem scan_eval {O : Type} (base : Store) (capacity active : ℕ) (word : List Symbol) (enabled : Bool) :
    (NativeHeader.scanRoutine (O := O)).eval ((setup (O := O)).eval (inputStore base capacity active word enabled)) =
      NativeHeader.encoded (scaffold base capacity active word)
        (NativeHeader.restrict (fieldState capacity word) enabled) [] := by
  rw [setup_eval, NativeHeader.scanRoutine_eval]
  have initial : (⟨word.tail, 0, true, enabled⟩ : ScanState) =
      NativeHeader.restrict ⟨word.tail, 0, true, true⟩ enabled := rfl
  rw [initial, NativeHeader.iterate_restrict]
  rfl

end ComplexityOfGenerators.Examples.PaddedCNF.NativeLiteral
