import ComplexityOfGenerators.Simulation.TransducerBank.UpToGeneration.Execution
import ComplexityOfGenerators.Proofs.Multitape.ResourceOrder

namespace ComplexityOfGenerators.Multitape

noncomputable section

variable {α : Type} [Fintype α]

theorem upTo_timeBudget_order (fallback : Word α) (copies : ℕ) (time : ℕ → ℕ)
    (dominates : ∀ n, n ≤ time n) :
    ResourceOrder (fun n => Simulation.TransducerBank.UpToGeneration.trialBudget fallback n
      (copies * (time n + 1))) time := by
  let alphabet := Fintype.card α + 10
  let coefficient := alphabet + 3 * copies + 2 + 3 * fallback.length + 5
  refine ⟨2 * coefficient, 1, by dsimp [coefficient, alphabet]; omega, ?_⟩
  intro n large
  have unit : 1 ≤ time n := large.trans (dominates n)
  have scan : alphabet * (n + 1) ≤ alphabet * (time n + 1) :=
    Nat.mul_le_mul_left _ (Nat.add_le_add_right (dominates n) 1)
  have length : 2 * n ≤ 2 * (time n + 1) := Nat.mul_le_mul_left _ ((dominates n).trans (Nat.le_succ _))
  have literal : 3 * fallback.length + 5 ≤ (3 * fallback.length + 5) * (time n + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (3 * fallback.length + 5)
      (show 1 ≤ time n + 1 by omega)
  calc
    Simulation.TransducerBank.UpToGeneration.trialBudget fallback n (copies * (time n + 1)) ≤
        alphabet * (time n + 1) + 3 * (copies * (time n + 1)) +
          2 * (time n + 1) + (3 * fallback.length + 5) * (time n + 1) := by
      unfold Simulation.TransducerBank.UpToGeneration.trialBudget
      change alphabet * (n + 1) + 3 * (copies * (time n + 1)) + 2 * n + 3 * fallback.length + 5 ≤ _
      omega
    _ = coefficient * (time n + 1) := by dsimp [coefficient]; ring
    _ ≤ coefficient * (2 * time n) := Nat.mul_le_mul_left _ (by omega)
    _ = (2 * coefficient) * time n := by ac_rfl

theorem upTo_spaceRadius_order (fallback : Word α) (copies : ℕ) (space : ℕ → ℕ)
    (dominates : ∀ n, n ≤ space n) :
    ResourceOrder (fun n => copies * (space n + 1) + 3 * n + fallback.length + 3) space := by
  let coefficient := copies + 3 + fallback.length + 3
  refine ⟨2 * coefficient, 1, by dsimp [coefficient]; omega, ?_⟩
  intro n large
  have unit : 1 ≤ space n := large.trans (dominates n)
  have length : 3 * n ≤ 3 * (space n + 1) := Nat.mul_le_mul_left _ ((dominates n).trans (Nat.le_succ _))
  have literal : fallback.length + 3 ≤ (fallback.length + 3) * (space n + 1) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (fallback.length + 3)
      (show 1 ≤ space n + 1 by omega)
  calc
    copies * (space n + 1) + 3 * n + fallback.length + 3 ≤
        copies * (space n + 1) + 3 * (space n + 1) + (fallback.length + 3) * (space n + 1) := by omega
    _ = coefficient * (space n + 1) := by dsimp [coefficient]; ring
    _ ≤ coefficient * (2 * space n) := Nat.mul_le_mul_left _ (by omega)
    _ = (2 * coefficient) * space n := by ac_rfl

end
end ComplexityOfGenerators.Multitape
