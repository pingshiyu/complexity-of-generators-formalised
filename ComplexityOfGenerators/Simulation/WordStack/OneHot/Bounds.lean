import ComplexityOfGenerators.Simulation.WordStack.OneHot.Model

namespace ComplexityOfGenerators.Simulation.WordStack.OneHot
variable {S O : Type} {k : ℕ}

theorem step_cost (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) :
    (step (O := O) slots encode).cost s ≤ 3*(s (slots 2)).length+4 := by
  cases position : s (slots 1) <;> cases pending : s (slots 2) <;>
    simp [step, Routine.branch, Routine.seq, Routine.clear, Routine.ofLocal, Local.push, Local.pop, Local.ticks,
      position, pending] <;> omega

theorem counted_cost (slots : Layout k) (encode : Bool → S) (s : Local.Store S k)
    (pending : (s (slots 2)).length ≤ 1) :
    (Routine.counted (slots 0) (step (O := O) slots encode)).cost s ≤ 9 := by
  let popped := Function.update s (slots 0) (s (slots 0)).tail
  have bound := step_cost (O := O) slots encode popped
  have flag : (popped (slots 2)).length ≤ 1 := by simpa [popped] using pending
  change 1+1+(step slots encode).cost popped ≤ 9
  omega

/-- Linear primitive cost, including resetting an arbitrary pending stack. -/
theorem routine_cost (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) :
    (routine (O := O) slots encode).cost s ≤ 11*(s (slots 0)).length+3*(s (slots 2)).length+3 := by
  let body := Routine.counted (slots 0) (step (O := O) slots encode)
  have loopBound := Routine.loopCost_bound body.cost body.eval (s (slots 0)).length 9
    (state slots encode s 0) (by
      intro i within
      rw [iterate_state]
      apply counted_cost
      simp only [state, Function.update_apply, show slots 2 ≠ slots 3 by simp,
        show slots 2 = slots 2 by rfl, ite_false, ite_true]
      split <;> simp)
  change (setup slots encode).cost s+1+
    Routine.loopCost body.cost body.eval ((setup slots encode).eval s (slots 0)).length
      ((setup slots encode).eval s) ≤ _
  rw [setup_state]
  have clock : (state slots encode s 0 (slots 0)).length = (s (slots 0)).length := by simp [state]
  rw [clock]
  have setupCost : (setup (O := O) slots encode).cost s = 3*(s (slots 2)).length+2 := by
    simp [setup, Routine.seq, Routine.clear, Routine.ofLocal, Local.push, Local.ticks]
  rw [setupCost]
  omega

/-- Storage stays within an existing budget when the caller reserves the
requested output length; all stacks outside the four owned slots are framed. -/
theorem routine_bound (slots : Layout k) (encode : Bool → S) (s : Local.Store S k) (budget : ℕ)
    (sizes : StoreBound s budget) (positive : 1 ≤ budget)
    (output : (s (slots 0)).length+(s (slots 3)).length ≤ budget) :
    StoreBound ((routine (O := O) slots encode).eval s) budget := by
  rw [routine_eval]
  unfold state
  apply StoreBound.update
  · apply StoreBound.update
    · apply StoreBound.update
      · exact sizes.update (slots 0) _ (by simp only [List.length_drop]; exact (Nat.sub_le _ _).trans (sizes (slots 0)))
      · simp only [List.length_drop]; exact (Nat.sub_le _ _).trans (sizes (slots 1))
    · split <;> simp_all
  · simpa using output

end ComplexityOfGenerators.Simulation.WordStack.OneHot
