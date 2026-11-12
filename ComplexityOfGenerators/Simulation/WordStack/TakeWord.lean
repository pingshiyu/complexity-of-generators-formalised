import ComplexityOfGenerators.Simulation.WordStack.StoreBounds
import ComplexityOfGenerators.Simulation.WordStack.RandomFree

namespace ComplexityOfGenerators.Simulation.WordStack.TakeWord

variable {S O : Type} {k : ℕ}

/-- Source, read-only unary width, forward output, clock, reverse buffer,
scratch. The source retains the suffix after the requested block. -/
abbrev Layout (k : ℕ) := Fin 6 ↪ Fin k

def setup (slots : Layout k) : Routine S O k :=
  (Routine.clearMany [slots 2,slots 4]).seq
    (Routine.assign (slots 1) (slots 3) (slots 5) (by simp) (by simp) (by simp) id)

def routine (slots : Layout k) : Routine S O k :=
  (setup slots).seq
    ((Blocks.routine (slots 3) (slots 0) (slots 4) (by simp) (by simp)).seq
      (Routine.transfer (slots 4) (slots 2) (by simp) id))

theorem setup_eval (slots : Layout k) (s : Local.Store S k) :
    (setup (O := O) slots).eval s =
      Function.update (Function.update (Function.update (Function.update s
        (slots 2) []) (slots 4) []) (slots 5) []) (slots 3) (s (slots 1)) := by
  funext j
  by_cases output : j=slots 2 <;> by_cases buffer : j=slots 4 <;>
    by_cases scratch : j=slots 5 <;> by_cases clock : j=slots 3 <;>
    simp [setup,Routine.seq,Routine.clearMany_eval,Routine.assign_eval,Function.update_apply,
      output,buffer,scratch,clock]

theorem routine_eval (slots : Layout k) (s : Local.Store S k) :
    (routine (O := O) slots).eval s =
      Function.update (Function.update (Function.update (Function.update (Function.update s
        (slots 5) []) (slots 3) []) (slots 4) [])
        (slots 0) ((s (slots 0)).drop (s (slots 1)).length))
        (slots 2) ((s (slots 0)).take (s (slots 1)).length) := by
  simp only [routine,Routine.seq,setup_eval,
    Blocks.routine_eval (slots 3) (slots 0) (slots 4) (by simp) (by simp) (by simp),Routine.transfer]
  funext j
  by_cases output : j=slots 2 <;> by_cases source : j=slots 0 <;> by_cases buffer : j=slots 4 <;>
    by_cases scratch : j=slots 5 <;> by_cases clock : j=slots 3 <;>
    simp [Function.update_apply,output,source,buffer,scratch,clock]

theorem routine_bound (slots : Layout k) (s : Local.Store S k) (budget : ℕ) (sizes : StoreBound s budget) :
    StoreBound ((routine (O := O) slots).eval s) budget := by
  rw [routine_eval]
  have dropBound : ((s (slots 0)).drop (s (slots 1)).length).length ≤ budget := by
    simp only [List.length_drop]
    exact (Nat.sub_le _ _).trans (sizes (slots 0))
  have takeBound : ((s (slots 0)).take (s (slots 1)).length).length ≤ budget := by
    simp only [List.length_take]
    exact (Nat.min_le_right _ _).trans (sizes (slots 0))
  exact ((((sizes.clear (slots 5)).clear (slots 3)).clear (slots 4)).update (slots 0) _ dropBound).update (slots 2) _ takeBound

theorem routine_cost (slots : Layout k) (s : Local.Store S k) (budget : ℕ) (sizes : StoreBound s budget) :
    (routine (O := O) slots).cost s ≤ 100*(budget+1) := by
  let a := (Routine.clearMany (O := O) [slots 2,slots 4]).eval s
  let b := (setup (O := O) slots).eval s
  let c := (Blocks.routine (O := O) (slots 3) (slots 0) (slots 4) (by simp) (by simp)).eval b
  have clearing := Routine.clearMany_cost (O := O) [slots 2,slots 4] s budget (fun j _ => sizes j)
  have aBound : StoreBound a budget := sizes.clearMany _
  have copying : (Routine.assign (O := O) (slots 1) (slots 3) (slots 5) (by simp) (by simp) (by simp) id).cost a ≤
      23*budget+3 := by
    have first := aBound (slots 1)
    have clock := aBound (slots 3)
    have scratch := aBound (slots 5)
    simp only [Routine.assign_cost]
    omega
  have blocking := Blocks.routine_cost (O := O) (slots 3) (slots 0) (slots 4) (by simp) (by simp) b
  have clock : (b (slots 3)).length = (s (slots 1)).length := by simp [b,setup_eval]
  rw [clock] at blocking
  have buffer : (c (slots 4)).length ≤ budget := by
    simp [c,b,Blocks.routine_eval,setup_eval]
    exact Or.inr (sizes (slots 0))
  have input := sizes (slots 1)
  change (setup (O := O) slots).cost s+1+
    ((Blocks.routine (O := O) (slots 3) (slots 0) (slots 4) (by simp) (by simp)).cost b+1+6*(c (slots 4)).length) ≤ _
  change (Routine.clearMany (O := O) [slots 2,slots 4]).cost s+1+
    (Routine.assign (O := O) (slots 1) (slots 3) (slots 5) (by simp) (by simp) (by simp) id).cost a+1+
    ((Blocks.routine (O := O) (slots 3) (slots 0) (slots 4) (by simp) (by simp)).cost b+1+6*(c (slots 4)).length) ≤ _
  simp only [List.length_cons,List.length_nil] at clearing
  omega

theorem routine_randomFree (slots : Layout k) : Command.RandomFree (routine (S := S) (O := O) slots).command := by
  simp [routine,setup,Blocks.routine,Blocks.body]

end ComplexityOfGenerators.Simulation.WordStack.TakeWord
