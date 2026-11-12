import ComplexityOfGenerators.Simulation.WordStack.OneHot.Basic

namespace ComplexityOfGenerators.Simulation.WordStack.OneHot
variable {S O : Type} {k : ℕ}

def state (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) (count : ℕ) : Local.Store S k :=
  Function.update (Function.update (Function.update (Function.update s
    (slots 0) ((s (slots 0)).drop count))
    (slots 1) ((s (slots 1)).drop count))
    (slots 2) (if count ≤ (s (slots 1)).length then [encode true] else []))
    (slots 3) (((List.range count).map (fun i => encode (decide (i = (s (slots 1)).length)))).reverse ++ s (slots 3))

theorem headNone_drop (word : List S) (count : ℕ) :
    (word.drop count).head?.isNone = decide (word.length ≤ count) := by
  by_cases bound : word.length ≤ count
  · have empty : word.drop count = [] := List.drop_eq_nil_iff.mpr bound
    simp [empty, bound]
  · cases head : (word.drop count).head? with
    | none =>
      have empty : word.drop count = [] := List.head?_eq_none_iff.mp head
      exact False.elim (bound (List.drop_eq_nil_iff.mp empty))
    | some a => simp [head, bound]

theorem state_bit (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) (count : ℕ) :
    bit slots (state slots encode s count) = decide (count = (s (slots 1)).length) := by
  by_cases below : count < (s (slots 1)).length
  · simp [bit, state, headNone_drop, show ¬ (s (slots 1)).length ≤ count by omega,
      show count ≠ (s (slots 1)).length by omega]
  · by_cases equal : count = (s (slots 1)).length
    · simp [bit, state, headNone_drop, equal]
    · simp [bit, state, headNone_drop, show (s (slots 1)).length ≤ count by omega,
        show ¬ count ≤ (s (slots 1)).length by omega, equal]

theorem setup_state (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) :
    (setup (O := O) slots encode).eval s = state slots encode s 0 := by
  rw [setup_eval]
  funext j
  by_cases clock : j = slots 0 <;> by_cases position : j = slots 1 <;>
    by_cases pending : j = slots 2 <;> by_cases output : j = slots 3 <;>
      simp [state, Function.update_apply, clock, position, pending, output]

theorem counted_state (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) (count : ℕ) :
    (Routine.counted (slots 0) (step (O := O) slots encode)).eval (state slots encode s count) =
      state slots encode s (count+1) := by
  have value : bit slots (Function.update (state slots encode s count) (slots 0)
      ((state slots encode s count (slots 0)).tail)) = decide (count = (s (slots 1)).length) := by
    simpa only [bit, Function.update_of_ne (show slots 1 ≠ slots 0 by simp),
      Function.update_of_ne (show slots 2 ≠ slots 0 by simp)] using state_bit slots encode s count
  funext j
  simp only [Routine.counted, Routine.seq, Routine.ofLocal, Local.eval_pop, step_eval, value]
  by_cases clock : j = slots 0
  · subst j
    simp [state, List.tail_drop]
  · by_cases position : j = slots 1
    · subst j
      simp [state, List.tail_drop]
    · by_cases pending : j = slots 2
      · subst j
        by_cases bound : (s (slots 1)).length ≤ count
        · simp [state, headNone_drop, bound, show ¬ count+1 ≤ (s (slots 1)).length by omega]
        · simp [state, headNone_drop, bound, show count ≤ (s (slots 1)).length by omega,
            show count+1 ≤ (s (slots 1)).length by omega]
      · by_cases output : j = slots 3
        · subst j
          simp [state, List.range_succ, List.reverse_append, List.append_assoc]
        · simp [state, Function.update_apply, clock, position, pending, output]

theorem iterate_state (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) (count : ℕ) :
    ((Routine.counted (slots 0) (step (O := O) slots encode)).eval^[count]) (state slots encode s 0) =
      state slots encode s count := by
  induction count with
  | zero => rfl
  | succ count ih => rw [Function.iterate_succ_apply', ih, counted_state]

/-- Exact reversed output, empty clock, saturated position countdown, and
pending marker. Positions outside the requested word produce only zeroes. -/
theorem routine_eval (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) :
    (routine (O := O) slots encode).eval s = state slots encode s (s (slots 0)).length := by
  simp only [routine, Routine.seq, setup_state, Routine.iterate]
  have clock : (state slots encode s 0 (slots 0)).length = (s (slots 0)).length := by simp [state]
  rw [clock, iterate_state]

end ComplexityOfGenerators.Simulation.WordStack.OneHot
