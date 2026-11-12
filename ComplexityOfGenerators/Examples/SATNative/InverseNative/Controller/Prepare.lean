import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Basic

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] NativeSubstitution.prepareStream LengthTest.routine

/-- The ordinary loader uses reversed stacks, with all other stacks blank. -/
def loaded (target label : List Symbol) : Memory :=
  ⟨(),0,0,[],Function.update (Function.update (fun _ => []) 0 target.reverse) 1 label.reverse⟩

def preparedStore (n : ℕ) (target label : List Symbol) : Store :=
  Function.update (Function.update (Function.update (Function.update (fun _ => []) 32
    (List.replicate n .zero)) 2 target) 3 label) 34 target

def prepared (n : ℕ) (target label : List Symbol) : Memory := ⟨(),n,0,[],preparedStore n target label⟩

theorem inputRoutine_value (n : ℕ) (target label : List Symbol) :
    inputRoutine.eval (Command.loadedIndex 32 .zero n (loaded target label)).store = preparedStore n target label := by
  funext j
  fin_cases j <;>
    simp [inputRoutine, Routine.seq, Routine.transfer, Routine.assign_eval,
      Command.loadedIndex, loaded, preparedStore, Memory.set]

theorem inputRoutine_cost (n : ℕ) (target label : List Symbol) :
    inputRoutine.cost (Command.loadedIndex 32 .zero n (loaded target label)).store =
      20*target.length+6*label.length+5 := by
  simp [inputRoutine, Routine.seq, Routine.transfer, Routine.assign_cost,
    Command.loadedIndex, loaded, Memory.set]
  omega

theorem prepared_bound (n : ℕ) (target label : List Symbol)
    (targetSize : target.length ≤ n) (labelSize : label.length ≤ n) : StoreBound (preparedStore n target label) n := by
  intro j
  by_cases a : j = 32 <;> by_cases b : j = 2 <;> by_cases c : j = 3 <;> by_cases d : j = 34 <;>
    simp [preparedStore, a, b, c, d] <;> assumption

theorem sizeTest_eval (s : Store) :
    sizeTest.eval s = Function.update (Function.update (Function.update (Function.update s 29 []) 28 []) 27 []) 33
      (if (s 34).length = (s 32).length then [.one] else []) := by
  change (LengthTest.routine (O := Symbol) sizeSlots .one).eval s = _
  simpa [sizeSlots] using LengthTest.routine_eval (O := Symbol) sizeSlots Symbol.one s

theorem sizeTest_flag (n : ℕ) (target label : List Symbol) :
    (sizeTest.eval (preparedStore n target label) 33).head?.isSome = decide (target.length = n) := by
  rw [sizeTest_eval]
  by_cases equal : target.length = n <;> simp [preparedStore,equal]

theorem sizeTest_frame (s : Store) (j : Fin 35)
    (a : j ≠ 29) (b : j ≠ 28) (c : j ≠ 27) (d : j ≠ 33) : sizeTest.eval s j = s j := by
  simp [sizeTest_eval, a,b,c,d]

theorem parse_here (s : Store) (j : Fin 32) :
    parse.eval s (slots j) = (NativeSubstitution.prepareStream (O := Symbol)).eval (s ∘ slots) j :=
  Routine.rename_eval_here _ _ _ _

theorem parse_upper (s : Store) (j : Fin 35) (upper : 32 ≤ j.val) : parse.eval s j = s j := by
  apply Routine.rename_eval_frame
  intro i equal
  have same := congrArg (fun j : Fin 35 => j.val) equal
  change j.val = i.val at same
  have := i.isLt
  omega

theorem moreRoutine_eval (s : Store) :
    moreRoutine.eval s = Function.update (Function.update (Function.update (Function.update s 9 []) 27
      ((s 4).drop (s 10).length)) 28 []) 29 [] := by
  simp only [moreRoutine, Routine.seq, Routine.assign_eval, Routine.clear,
    DrainPair.routine_eval (28 : Fin 35) 27 29 (by decide) (by decide) (by decide)]
  funext j
  by_cases a : j = 9 <;> by_cases b : j = 27 <;> by_cases c : j = 28 <;> by_cases d : j = 29 <;>
    simp [a,b,c,d]

theorem moreRoutine_frame (s : Store) (j : Fin 35)
    (a : j ≠ 9) (b : j ≠ 27) (c : j ≠ 28) (d : j ≠ 29) : moreRoutine.eval s j = s j := by
  simp [moreRoutine_eval,a,b,c,d]

theorem moreRoutine_flag (s : Store) (capacity active : ℕ)
    (cap : s 4 = List.replicate capacity .one) (count : s 10 = List.replicate active .one) :
    (moreRoutine.eval s 27).head?.isSome = decide (active+1 ≤ capacity) := by
  cases remaining : capacity-active with
  | zero =>
      have failed : ¬active+1 ≤ capacity := by omega
      simp [moreRoutine_eval,cap,count,remaining,failed]
  | succ rest =>
      have enough : active+1 ≤ capacity := by omega
      simp [moreRoutine_eval,cap,count,remaining,enough]

theorem moreRoutine_preserves (s : Store) (budget : ℕ) (sizes : StoreBound s budget) : StoreBound (moreRoutine.eval s) budget := by
  rw [moreRoutine_eval]
  exact (((sizes.clear 9).update 27 _ (by simpa only [List.length_drop] using (Nat.sub_le _ _).trans (sizes 4))).clear 28).clear 29

theorem transform_here (bit : Bool) (s : Store) (j : Fin 32) :
    (transform bit).eval s (slots j) = (bodyTransform (O := Symbol) bit).eval (s ∘ slots) j :=
  Routine.rename_eval_here _ _ _ _

theorem transform_upper (bit : Bool) (s : Store) (j : Fin 35) (upper : 32 ≤ j.val) :
    (transform bit).eval s j = s j := by
  apply Routine.rename_eval_frame
  intro i equal
  have same := congrArg (fun j : Fin 35 => j.val) equal
  change j.val = i.val at same
  have := i.isLt
  omega

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
