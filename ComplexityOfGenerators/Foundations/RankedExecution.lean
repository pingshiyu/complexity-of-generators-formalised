import ComplexityOfGenerators.Foundations.ExecutionBounds

/-! A decreasing natural-valued rank gives an actual transition bound.  Both
the invariant and its terminal postcondition refer to the existing native
transition evaluator. -/

namespace ComplexityOfGenerators.Machine

variable {I A O : Type} (M : Machine I A O)

theorem runFrom_of_rank (data : InputData I A) (bits : BitString)
    (invariant : Configuration M → Prop) (rank : Configuration M → ℕ)
    (post : Outcome O → Prop)
    (terminal : ∀ c result, invariant c → M.observe data bits c = .halted result → post result)
    (decreases : ∀ c d, invariant c → M.observe data bits c = .running c →
      M.next data bits c = .running d → invariant d ∧ rank d < rank c)
    (c : Configuration M) (valid : invariant c) :
    ∃ result, M.runFrom data bits c (rank c) = .halted result ∧ post result := by
  have aux : ∀ k c, rank c = k → invariant c →
      ∃ result, M.runFrom data bits c k = .halted result ∧ post result := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
        intro c equal valid
        cases observation : M.observe data bits c with
        | halted result =>
            exact ⟨result, M.runFrom_halted data bits c result observation k,
              terminal c result valid observation⟩
        | running current =>
            have same := M.observe_running_eq data bits c current observation
            subst current
            obtain ⟨d, next⟩ := M.next_running_of_observe_running data bits c observation
            obtain ⟨valid', less⟩ := decreases c d valid observation next
            obtain ⟨result, execution, related⟩ := ih (rank d) (by omega) d rfl valid'
            have shifted := M.runFrom_shift data bits c d observation next (rank d)
            rw [execution] at shifted
            refine ⟨result, ?_, related⟩
            have padded := M.runFrom_halted_add data bits c (rank d + 1) result shifted (k - (rank d + 1))
            simpa only [Nat.add_sub_of_le (by omega : rank d + 1 ≤ k)] using padded
  exact aux (rank c) c rfl valid

end ComplexityOfGenerators.Machine
