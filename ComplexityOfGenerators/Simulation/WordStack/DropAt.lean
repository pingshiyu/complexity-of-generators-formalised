import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Simulation.WordStack.DropAt

variable {S O : Type} {k : ℕ}

/-- Word, read-only unary position, reversed prefix, clock, scratch. -/
abbrev Layout (k : ℕ) := Fin 5 ↪ Fin k

def setup (slots : Layout k) (unit : S) : Routine S O k :=
  (Routine.clear (slots 2)).seq
    (Routine.assign (slots 1) (slots 3) (slots 4) (by simp) (by simp) (by simp) (fun _ => unit))

def routine (slots : Layout k) (unit : S) : Routine S O k :=
  (setup slots unit).seq
    ((Blocks.routine (slots 3) (slots 0) (slots 2) (by simp) (by simp)).seq
      ((Routine.ofLocal (Local.pop (slots 0))).seq
        ((Routine.transfer (slots 0) (slots 2) (by simp) id).seq
          (Routine.transfer (slots 2) (slots 0) (by simp) id))))

theorem setup_eval (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (setup (O := O) slots unit).eval s =
      Function.update (Function.update (Function.update s (slots 2) []) (slots 4) [])
        (slots 3) (List.replicate (s (slots 1)).length unit) := by
  simp [setup, Routine.seq, Routine.assign_eval, Routine.clear, List.map_const']

/-- A native word erasure, including positions beyond the end of the word.
The source is restored in forward order and every temporary stack is empty. -/
theorem routine_eval (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (routine (O := O) slots unit).eval s =
      Function.update (Function.update (Function.update (Function.update s
        (slots 4) []) (slots 3) []) (slots 2) []) (slots 0) ((s (slots 0)).eraseIdx (s (slots 1)).length) := by
  simp only [routine, Routine.seq, setup_eval,
    Blocks.routine_eval (slots 3) (slots 0) (slots 2) (by simp) (by simp) (by simp),
    Routine.ofLocal, Local.eval_pop, Routine.transfer]
  funext j
  by_cases word : j = slots 0 <;> by_cases prefixWord : j = slots 2 <;>
    by_cases clock : j = slots 3 <;> by_cases scratch : j = slots 4 <;>
    simp [Function.update_apply, word, prefixWord, clock, scratch, List.map_id,
      List.reverse_append, List.eraseIdx_eq_take_drop_succ, List.tail_drop]

theorem routine_bound (slots : Layout k) (unit : S) (s : Local.Store S k) (budget : ℕ)
    (sizes : StoreBound s budget) : StoreBound ((routine (O := O) slots unit).eval s) budget := by
  rw [routine_eval]
  apply (((sizes.clear (slots 4)).clear (slots 3)).clear (slots 2)).update (slots 0)
  exact (List.length_eraseIdx_le _ _).trans (sizes (slots 0))

theorem routine_cost (slots : Layout k) (unit : S) (s : Local.Store S k) (budget : ℕ)
    (sizes : StoreBound s budget) : (routine (O := O) slots unit).cost s ≤ 60 * (budget + 1) := by
  let a := (setup (O := O) slots unit).eval s
  let b := (Blocks.routine (O := O) (slots 3) (slots 0) (slots 2) (by simp) (by simp)).eval a
  let c := (Routine.ofLocal (O := O) (Local.pop (slots 0))).eval b
  let d := (Routine.transfer (O := O) (slots 0) (slots 2) (by simp) id).eval c
  have blockCost := Blocks.routine_cost (O := O) (slots 3) (slots 0) (slots 2) (by simp) (by simp) a
  have counter : (a (slots 3)).length = (s (slots 1)).length := by simp [a, setup_eval]
  rw [counter] at blockCost
  have rest : (c (slots 0)).length ≤ (s (slots 0)).length := by
    simp [c, b, a, setup_eval, Blocks.routine_eval, Routine.ofLocal, Local.eval_pop, List.length_tail,
      Action.apply]
  have total : (d (slots 2)).length ≤ (s (slots 0)).length := by
    simp [d, c, b, a, setup_eval, Blocks.routine_eval, Routine.transfer, Routine.ofLocal, Local.eval_pop,
      List.length_tail, Action.apply]
    omega
  have word := sizes (slots 0)
  have position := sizes (slots 1)
  have reversed := sizes (slots 2)
  have clock := sizes (slots 3)
  have scratch := sizes (slots 4)
  change (setup (O := O) slots unit).cost s + 1 +
    ((Blocks.routine (O := O) (slots 3) (slots 0) (slots 2) (by simp) (by simp)).cost a + 1 +
      (1 + 1 + (6 * (c (slots 0)).length + 1 + 6 * (d (slots 2)).length))) ≤ _
  simp only [setup, Routine.seq, Routine.clear, Routine.assign_cost]
  simp only [Function.update_apply, show slots 1 ≠ slots 2 by simp,
    show slots 3 ≠ slots 2 by simp, show slots 4 ≠ slots 2 by simp, ↓reduceIte]
  omega

theorem routine_randomFree (slots : Layout k) (unit : S) : Command.RandomFree (routine (O := O) slots unit).command := by
  simp [routine, setup, Blocks.routine, Blocks.body]

end ComplexityOfGenerators.Simulation.WordStack.DropAt
