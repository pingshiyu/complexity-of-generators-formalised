import ComplexityOfGenerators.Simulation.WordStack.PolynomialCounters
import ComplexityOfGenerators.Simulation.WordStack.Routines

namespace ComplexityOfGenerators.Simulation.WordStack.CounterRoutine

variable {S O : Type} {k : ℕ}

/-- Source word, result counter, base, temporary stack, and scratch stack. -/
abbrev Layout (k : ℕ) := Fin 5 ↪ Fin k

def setup (slots : Layout k) (unit : S) : Routine S O k :=
  (Routine.assign (slots 0) (slots 2) (slots 4) (by simp) (by simp) (by simp) (fun _ => unit)).seq
    ((Routine.ofLocal (Local.push (slots 2) unit)).seq (Routine.clear (slots 3)))

theorem setup_eval (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (setup (O := O) slots unit).eval s =
      Function.update (Function.update (Function.update s (slots 4) [])
        (slots 2) (List.replicate ((s (slots 0)).length + 1) unit)) (slots 3) [] := by
  simp [setup, Routine.seq, Routine.assign_eval, Routine.ofLocal, Local.eval_push,
    Routine.clear, Function.update_idem, List.replicate_succ]

theorem setup_cost (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (setup (O := O) slots unit).cost s =
      3 * (s (slots 2)).length + 3 * (s (slots 4)).length + 14 * (s (slots 0)).length +
        3 * (s (slots 3)).length + 6 := by
  simp [setup, Routine.seq, Routine.assign_cost, Routine.assign_eval, Routine.ofLocal,
    Local.push, Local.ticks, Routine.clear, Local.eval]
  ring

def routine (slots : Layout k) (p : PolynomialBound) (unit : S) : Routine S O k where
  command := (setup slots unit).command.seq
    (Command.polynomialCounter p (slots 1) (slots 2) (slots 3) (slots 4) unit)
  eval := fun s => Function.update ((setup (O := O) slots unit).eval s) (slots 1)
    (List.replicate (p (s (slots 0)).length) unit)
  cost := fun s => (setup (O := O) slots unit).cost s + 1 +
    Command.counterTicks p (s (slots 0)).length (s (slots 1)).length
  runs bits m bounded := by
    obtain ⟨t, cost, first⟩ := (setup slots unit).runs bits m bounded
    let middle : Memory S O k := {m with store := (setup (O := O) slots unit).eval m.store}
    have last := Command.polynomialCounter_runs p (slots 1) (slots 2) (slots 3) (slots 4)
      (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) unit (m.store (slots 0)).length bits
      middle bounded (by simp [middle, setup_eval]) (by simp [middle, setup_eval]) (by simp [middle, setup_eval])
    have value : middle.store (slots 1) = m.store (slots 1) := by simp [middle, setup_eval]
    rw [value] at last
    exact ⟨t + 1 + Command.counterTicks p (m.store (slots 0)).length (m.store (slots 1)).length,
      by omega, Command.Runs.seq _ _ _ _ _ _ _ first last⟩

theorem routine_eval (slots : Layout k) (p : PolynomialBound) (unit : S) (s : Local.Store S k) :
    (routine (O := O) slots p unit).eval s =
      Function.update (Function.update (Function.update (Function.update s (slots 4) [])
        (slots 2) (List.replicate ((s (slots 0)).length + 1) unit)) (slots 3) [])
        (slots 1) (List.replicate (p (s (slots 0)).length) unit) := by
  simp only [routine, setup_eval]

theorem routine_cost (slots : Layout k) (p : PolynomialBound) (unit : S) (s : Local.Store S k)
    (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (routine (O := O) slots p unit).cost s ≤
      26 * budget + 7 + Command.counterBudget p (s (slots 0)).length := by
  have counter := Command.counterTicks_bound p (s (slots 0)).length (s (slots 1)).length
  have h₀ := sizes (slots 0)
  have h₁ := sizes (slots 1)
  have h₂ := sizes (slots 2)
  have h₃ := sizes (slots 3)
  have h₄ := sizes (slots 4)
  simp only [routine, setup_cost]
  omega

end ComplexityOfGenerators.Simulation.WordStack.CounterRoutine
