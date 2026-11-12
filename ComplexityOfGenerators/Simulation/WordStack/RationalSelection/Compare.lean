import ComplexityOfGenerators.Simulation.WordStack.LengthTest

/-! A verified unary strict comparison used by bounded rational selection. -/

namespace ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare

variable {S O : Type} {k : ℕ}

/-- Threshold, value, result flag, threshold copy, value counter, scratch. -/
abbrev Layout (k : ℕ) := Fin 6 ↪ Fin k

def setup (slots : Layout k) (unit : S) : Routine S O k :=
  (Routine.assign (slots 0) (slots 3) (slots 5) (by simp) (by simp) (by simp) id).seq
  ((Routine.assign (slots 1) (slots 4) (slots 5) (by simp) (by simp) (by simp) (fun _ => unit)).seq
    (Routine.clear (slots 2)))

theorem setup_eval (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (setup (O := O) slots unit).eval s =
      Function.update (Function.update (Function.update (Function.update s (slots 5) [])
        (slots 3) (s (slots 0))) (slots 4) (List.replicate (s (slots 1)).length unit)) (slots 2) [] := by
  funext j
  by_cases flag : j = slots 2 <;> by_cases copy : j = slots 3 <;>
    by_cases counter : j = slots 4 <;> by_cases scratch : j = slots 5 <;>
      simp [setup, Routine.seq, Routine.assign_eval, Routine.clear,
        flag, copy, counter, scratch]

def finish (word flag : Fin k) (unit : S) : Local S k :=
  .read word fun head => if head.isSome then Local.push flag unit else .skip

theorem finish_eval (word flag : Fin k) (unit : S) (s : Local.Store S k) :
    (finish word flag unit).eval s = Function.update s flag
      (if (s word).head?.isSome then unit :: s flag else s flag) := by
  cases head : (s word).head? <;>
    simp [finish, Local.eval_read, Local.eval_push, head, Function.update_eq_self]

def routine (slots : Layout k) (unit : S) : Routine S O k :=
  (setup slots unit).seq
  ((DrainPair.routine (slots 4) (slots 3) (slots 2) (by simp) (by simp)).seq
  ((Routine.ofLocal (finish (slots 3) (slots 2) unit)).seq (Routine.clear (slots 3))))

theorem remaining_nonempty (word : List S) (value : ℕ) :
    (word.drop value).head?.isSome = decide (value < word.length) := by
  by_cases less : value < word.length
  · have nonempty : word.drop value ≠ [] := by
      intro empty
      have := List.drop_eq_nil_iff.mp empty
      omega
    cases remainder : word.drop value with
    | nil => contradiction
    | cons head rest => simp [less]
  · have empty := List.drop_eq_nil_iff.mpr (show word.length ≤ value by omega)
    simp [empty, less]

theorem routine_eval (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (routine (O := O) slots unit).eval s =
      Function.update (Function.update (Function.update (Function.update s (slots 5) [])
        (slots 4) []) (slots 3) []) (slots 2)
        (if (s (slots 1)).length < (s (slots 0)).length then [unit] else []) := by
  simp only [routine, Routine.seq, setup_eval,
    DrainPair.routine_eval (slots 4) (slots 3) (slots 2) (by simp) (by simp) (by simp),
    Routine.ofLocal, finish_eval, Routine.clear]
  funext j
  by_cases flag : j = slots 2 <;> by_cases copy : j = slots 3 <;>
    by_cases counter : j = slots 4 <;> by_cases scratch : j = slots 5 <;>
      simp_all

theorem setup_cost (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (setup (O := O) slots unit).cost s =
      3 * (s (slots 3)).length + 3 * (s (slots 5)).length + 14 * (s (slots 0)).length +
        3 * (s (slots 4)).length + 14 * (s (slots 1)).length + 3 * (s (slots 2)).length + 8 := by
  simp [setup, Routine.seq, Routine.assign_cost, Routine.assign_eval, Routine.clear]
  ring

theorem finish_ticks (word flag : Fin k) (unit : S) (s : Local.Store S k) :
    (finish word flag unit).ticks s ≤ 2 := by
  cases head : (s word).head? <;> simp [finish, Local.ticks, Local.push, head]

theorem routine_cost (slots : Layout k) (unit : S) (s : Local.Store S k)
    (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (routine (O := O) slots unit).cost s ≤ 80 * (budget + 1) := by
  let prepared := (setup (O := O) slots unit).eval s
  let drained := (DrainPair.routine (O := O) (slots 4) (slots 3) (slots 2) (by simp) (by simp)).eval prepared
  have first := DrainPair.routine_cost (O := O) (slots 4) (slots 3) (slots 2) (by simp) (by simp) prepared
  have last := finish_ticks (slots 3) (slots 2) unit drained
  have remaining : ((finish (slots 3) (slots 2) unit).eval drained (slots 3)).length ≤ (s (slots 0)).length := by
    simp [finish_eval, drained, prepared,
      DrainPair.routine_eval (slots 4) (slots 3) (slots 2) (by simp) (by simp) (by simp), setup_eval]
  have counter : (prepared (slots 4)).length = (s (slots 1)).length := by simp [prepared, setup_eval]
  rw [counter] at first
  have h₀ := sizes (slots 0)
  have h₁ := sizes (slots 1)
  have h₂ := sizes (slots 2)
  have h₃ := sizes (slots 3)
  have h₄ := sizes (slots 4)
  have h₅ := sizes (slots 5)
  change (setup slots unit).cost s + 1 +
    ((DrainPair.routine (slots 4) (slots 3) (slots 2) (by simp) (by simp)).cost prepared + 1 +
    ((finish (slots 3) (slots 2) unit).ticks drained + 1 +
      3 * ((finish (slots 3) (slots 2) unit).eval drained (slots 3)).length)) ≤ _
  rw [setup_cost]
  omega

end ComplexityOfGenerators.Simulation.WordStack.RationalSelection.Compare
