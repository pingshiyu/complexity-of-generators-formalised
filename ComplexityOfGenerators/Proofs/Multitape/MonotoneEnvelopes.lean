import ComplexityOfGenerators.Proofs.Multitape.ResourceOrder
import ComplexityOfGenerators.Proofs.Multitape.FiniteInputBounds
import ComplexityOfGenerators.Simulation.TransducerBank.RegionSteps

namespace ComplexityOfGenerators.Multitape

/-- Eventual source bounds, including small inputs, have one fixed envelope for
all lengths at most n. Monotonicity is exactly the paper's additional premise. -/
theorem monotone_resource_envelope {resource target : ℕ → ℕ}
    (order : ResourceOrder resource target) (monotone : Monotone target) :
    ∃ copies : ℕ, 0 < copies ∧ ∀ n m, m ≤ n → resource m ≤ copies * (target n + 1) := by
  obtain ⟨copies, positive, bounded⟩ := ResourceOrder.global_affine order
  refine ⟨copies, positive, ?_⟩
  intro n m small
  exact (bounded m).trans (Nat.mul_le_mul_left copies
    (Nat.add_le_add_right (monotone small) 1))

variable {α O : Type} [Fintype α]

theorem monotone_time_envelope (M : MultitapeMachine α Bool O)
    (resource target : ℕ → ℕ) (order : ResourceOrder resource target) (monotone : Monotone target)
    (bounded : ∀ word, M.TimeBound (decisionData word) (resource word.length)) :
    ∃ copies : ℕ, 0 < copies ∧ ∀ n word, word.length ≤ n →
      M.TimeBound (decisionData word) (copies * (target n + 1)) := by
  obtain ⟨copies, positive, covers⟩ := monotone_resource_envelope order monotone
  exact ⟨copies, positive, fun n word small =>
    (bounded word).mono (covers n word.length small)⟩

/-- Actual all-tape visited-cell bounds imply the radius bound needed by the
finite source simulator, with a single envelope for all proposed words. -/
theorem monotone_space_envelope (M : MultitapeMachine α Bool O)
    (resource target : ℕ → ℕ) (order : ResourceOrder resource target) (monotone : Monotone target)
    (bounded : ∀ word, M.CellSpaceBound (decisionData word) (resource word.length)) :
    ∃ copies : ℕ, 0 < copies ∧ ∀ n word, word.length ≤ n →
      M.SpaceBound (decisionData word) (copies * (target n + 1)) := by
  obtain ⟨copies, positive, covers⟩ := monotone_resource_envelope order monotone
  refine ⟨copies, positive, ?_⟩
  intro n word small bits used config path
  have original := M.radiusSpaceBound_of_cells (decisionData word) (resource word.length) (bounded word)
  exact (original bits used config path).mono M.program (covers n word.length small)

end ComplexityOfGenerators.Multitape
