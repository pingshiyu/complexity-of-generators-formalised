import ComplexityOfGenerators.Simulation.WordStack.DropAt

/-! Native insertion into a stored word. Positions beyond the end append;
inside the word this agrees with the standard ordered `List.insertIdx`. -/

namespace ComplexityOfGenerators.Simulation.WordStack.InsertAt

variable {S O : Type} {k : ℕ}

abbrev Layout (k : ℕ) := DropAt.Layout k

/-- Word, read-only unary position, reversed prefix, clock, scratch. -/
def routine (slots : Layout k) (unit letter : S) : Routine S O k :=
  (DropAt.setup slots unit).seq
    ((Blocks.routine (slots 3) (slots 0) (slots 2) (by simp) (by simp)).seq
      ((Routine.ofLocal (Local.push (slots 2) letter)).seq
        ((Routine.transfer (slots 0) (slots 2) (by simp) id).seq
          (Routine.transfer (slots 2) (slots 0) (by simp) id))))

def insertAt (word : List S) (position : ℕ) (letter : S) : List S :=
  word.take position ++ [letter] ++ word.drop position

theorem insertAt_length (word : List S) (position : ℕ) (letter : S) :
    (insertAt word position letter).length = word.length+1 := by
  simp only [insertAt,List.length_append,List.length_take,List.length_singleton,List.length_drop]
  omega

theorem insertAt_eq_insertIdx (word : List S) (position : ℕ) (letter : S) (inside : position ≤ word.length) :
    insertAt word position letter = word.insertIdx position letter := by
  induction word generalizing position with
  | nil =>
      have zero : position=0 := by simpa using inside
      subst position
      rfl
  | cons first rest ih =>
      cases position with
      | zero => rfl
      | succ position => simpa [insertAt] using congrArg (first :: ·) (ih position (by simp only [List.length_cons] at inside; omega))

/-- The real finite controller restores the inserted word in forward order
and empties every temporary stack, while preserving the unary position. -/
theorem routine_eval (slots : Layout k) (unit letter : S) (s : Local.Store S k) :
    (routine (O := O) slots unit letter).eval s =
      Function.update (Function.update (Function.update (Function.update s
        (slots 4) []) (slots 3) []) (slots 2) []) (slots 0) (insertAt (s (slots 0)) (s (slots 1)).length letter) := by
  simp only [routine,Routine.seq,DropAt.setup_eval,
    Blocks.routine_eval (slots 3) (slots 0) (slots 2) (by simp) (by simp) (by simp),
    Routine.ofLocal,Local.eval_push,Routine.transfer]
  funext j
  by_cases word : j=slots 0 <;> by_cases buffer : j=slots 2 <;>
    by_cases clock : j=slots 3 <;> by_cases scratch : j=slots 4 <;>
    simp [Function.update_apply,word,buffer,clock,scratch,List.map_id,
      List.reverse_append,insertAt,List.append_assoc]

theorem routine_bound (slots : Layout k) (unit letter : S) (s : Local.Store S k) (budget : ℕ)
    (sizes : StoreBound s budget) : StoreBound ((routine (O := O) slots unit letter).eval s) (budget+1) := by
  rw [routine_eval]
  apply ((((sizes.mono (Nat.le_succ budget)).clear (slots 4)).clear (slots 3)).clear (slots 2)).update (slots 0)
  rw [insertAt_length]
  exact Nat.add_le_add_right (sizes (slots 0)) 1

theorem routine_preserves_cap (slots : Layout k) (unit letter : S) (s : Local.Store S k) (budget : ℕ)
    (sizes : StoreBound s budget) (room : (s (slots 0)).length+1 ≤ budget) :
    StoreBound ((routine (O := O) slots unit letter).eval s) budget := by
  rw [routine_eval]
  apply (((sizes.clear (slots 4)).clear (slots 3)).clear (slots 2)).update (slots 0)
  simpa only [insertAt_length] using room

theorem routine_cost (slots : Layout k) (unit letter : S) (s : Local.Store S k) (budget : ℕ)
    (sizes : StoreBound s budget) : (routine (O := O) slots unit letter).cost s ≤ 60*(budget+2) := by
  let a := (DropAt.setup (O := O) slots unit).eval s
  let b := (Blocks.routine (O := O) (slots 3) (slots 0) (slots 2) (by simp) (by simp)).eval a
  let c := (Routine.ofLocal (O := O) (Local.push (slots 2) letter)).eval b
  let d := (Routine.transfer (O := O) (slots 0) (slots 2) (by simp) id).eval c
  have blockCost := Blocks.routine_cost (O := O) (slots 3) (slots 0) (slots 2) (by simp) (by simp) a
  have counter : (a (slots 3)).length = (s (slots 1)).length := by simp [a,DropAt.setup_eval]
  rw [counter] at blockCost
  have rest : (c (slots 0)).length ≤ (s (slots 0)).length := by
    simp [c,b,a,DropAt.setup_eval,Blocks.routine_eval,Routine.ofLocal,Local.eval_push]
  have total : (d (slots 2)).length = (s (slots 0)).length+1 := by
    simp [d,c,b,a,DropAt.setup_eval,Blocks.routine_eval,Routine.transfer,Routine.ofLocal,Local.eval_push]
    omega
  have word := sizes (slots 0)
  have position := sizes (slots 1)
  have reversed := sizes (slots 2)
  have clock := sizes (slots 3)
  have scratch := sizes (slots 4)
  change (DropAt.setup (O := O) slots unit).cost s+1+
    ((Blocks.routine (O := O) (slots 3) (slots 0) (slots 2) (by simp) (by simp)).cost a+1+
      (1+1+(6*(c (slots 0)).length+1+6*(d (slots 2)).length))) ≤ _
  simp only [DropAt.setup,Routine.seq,Routine.clear,Routine.assign_cost]
  simp only [Function.update_apply,show slots 1 ≠ slots 2 by simp,
    show slots 3 ≠ slots 2 by simp,show slots 4 ≠ slots 2 by simp,↓reduceIte]
  omega

theorem routine_randomFree (slots : Layout k) (unit letter : S) :
    Command.RandomFree (routine (O := O) slots unit letter).command := by
  simp [routine,DropAt.setup,Blocks.routine,Blocks.body]

end ComplexityOfGenerators.Simulation.WordStack.InsertAt
