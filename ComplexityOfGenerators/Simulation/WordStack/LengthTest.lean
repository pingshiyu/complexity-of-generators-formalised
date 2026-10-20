import ComplexityOfGenerators.Simulation.WordStack.DrainPair

namespace ComplexityOfGenerators.Simulation.WordStack.LengthTest

variable {S O : Type} {k : ℕ}

/-- Word, comparison word, result flag, copy, counter, scratch. -/
abbrev Layout (k : ℕ) := Fin 6 ↪ Fin k

def setup (slots : Layout k) (unit : S) : Routine S O k :=
  (Routine.assign (slots 1) (slots 4) (slots 5) (by simp) (by simp) (by simp) (fun _ => unit)).seq
  ((Routine.assign (slots 0) (slots 3) (slots 5) (by simp) (by simp) (by simp) id).seq
  ((Routine.clear (slots 2)).seq (Routine.ofLocal (Local.push (slots 2) unit))))

def finishCode (word flag : Fin k) : Local S k :=
  .read word fun head => if head.isSome then Local.pop flag else .skip

theorem finish_eval (word flag : Fin k) (s : Local.Store S k) :
    (finishCode word flag).eval s = Function.update s flag
      (if (s word).head?.isSome then (s flag).tail else s flag) := by
  cases h : (s word).head? <;> simp [finishCode, Local.eval_read, h, Function.update_eq_self]

def routine (slots : Layout k) (unit : S) : Routine S O k :=
  (setup slots unit).seq
  ((DrainPair.routine (slots 4) (slots 3) (slots 2) (by simp) (by simp)).seq
  ((Routine.ofLocal (finishCode (slots 3) (slots 2))).seq (Routine.clear (slots 3))))

theorem setup_eval (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (setup (O := O) slots unit).eval s =
      Function.update (Function.update (Function.update (Function.update s (slots 5) [])
        (slots 4) (List.replicate (s (slots 1)).length unit)) (slots 3) (s (slots 0))) (slots 2) [unit] := by
  funext j
  by_cases h₂ : j = slots 2 <;> by_cases h₃ : j = slots 3 <;>
    by_cases h₄ : j = slots 4 <;> by_cases h₅ : j = slots 5 <;>
      simp [setup, Routine.seq, Routine.assign_eval, Routine.ofLocal, Routine.clear,
        Local.eval_push, Function.update_apply, h₂, h₃, h₄, h₅]

theorem result_eq (unit : S) (word : List S) (n : ℕ) :
    (if (word.drop n).head?.isSome then ([unit].drop (n - word.length)).tail
      else [unit].drop (n - word.length)) = if word.length = n then [unit] else [] := by
  cases remainder : word.drop n with
  | nil =>
    have bound : word.length ≤ n := List.drop_eq_nil_iff.mp remainder
    by_cases equal : word.length = n
    · simp [equal]
    · have tail : [unit].drop (n - word.length) = [] :=
        List.drop_eq_nil_of_le (by simp; omega)
      simp [equal, tail]
  | cons a rest =>
    have length := congrArg List.length remainder
    simp only [List.length_drop, List.length_cons] at length
    have bound : n ≤ word.length := by omega
    simp [Nat.sub_eq_zero_of_le bound, show word.length ≠ n by omega]

theorem routine_eval (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (routine (O := O) slots unit).eval s =
      Function.update (Function.update (Function.update (Function.update s (slots 5) []) (slots 4) [])
        (slots 3) []) (slots 2) (if (s (slots 0)).length = (s (slots 1)).length then [unit] else []) := by
  simp only [routine, Routine.seq, setup_eval, DrainPair.routine_eval (slots 4) (slots 3) (slots 2) (by simp) (by simp) (by simp),
    Routine.ofLocal, finish_eval, Routine.clear]
  funext j
  by_cases h₂ : j = slots 2 <;> by_cases h₃ : j = slots 3 <;>
    by_cases h₄ : j = slots 4 <;> by_cases h₅ : j = slots 5 <;>
      simp_all [Function.update_apply]
  simpa using result_eq unit (s (slots 0)) (s (slots 1)).length

theorem setup_cost (slots : Layout k) (unit : S) (s : Local.Store S k) :
    (setup (O := O) slots unit).cost s =
      3 * (s (slots 4)).length + 3 * (s (slots 5)).length + 14 * (s (slots 1)).length +
      3 * (s (slots 3)).length + 14 * (s (slots 0)).length + 3 * (s (slots 2)).length + 10 := by
  simp [setup, Routine.seq, Routine.assign_cost, Routine.assign_eval, Routine.ofLocal,
    Routine.clear, Local.ticks, Local.push]
  ring

theorem finish_ticks (word flag : Fin k) (s : Local.Store S k) : (finishCode word flag).ticks s ≤ 2 := by
  cases h : (s word).head? <;> simp [finishCode, Local.ticks, Local.pop, h]

theorem routine_cost (slots : Layout k) (unit : S) (s : Local.Store S k)
    (budget : ℕ) (sizes : ∀ j, (s j).length ≤ budget) :
    (routine (O := O) slots unit).cost s ≤ 80 * (budget + 1) := by
  let prepared := (setup (O := O) slots unit).eval s
  let drained := (DrainPair.routine (O := O) (slots 4) (slots 3) (slots 2) (by simp) (by simp)).eval prepared
  have first := DrainPair.routine_cost (O := O) (slots 4) (slots 3) (slots 2) (by simp) (by simp) prepared
  have last := finish_ticks (slots 3) (slots 2) drained
  have remaining : ((finishCode (slots 3) (slots 2)).eval drained (slots 3)).length ≤ (s (slots 0)).length := by
    simp [finish_eval, drained, prepared, DrainPair.routine_eval (slots 4) (slots 3) (slots 2) (by simp) (by simp) (by simp), setup_eval]
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
    ((finishCode (slots 3) (slots 2)).ticks drained + 1 +
    3 * ((finishCode (slots 3) (slots 2)).eval drained (slots 3)).length)) ≤ _
  rw [setup_cost]
  omega

end ComplexityOfGenerators.Simulation.WordStack.LengthTest
