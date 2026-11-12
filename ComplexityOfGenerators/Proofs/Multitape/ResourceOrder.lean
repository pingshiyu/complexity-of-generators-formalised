import ComplexityOfGenerators.MultitapeComplexityClasses
import Mathlib.Data.Finset.Lattice.Fold

namespace ComplexityOfGenerators.Multitape.ResourceOrder

/-- Finitely many small inputs can be covered by one fixed clock multiplier.
This does not change O(t) into a pointwise O(t) assertion when t can vanish:
the explicitly constructed clock is c*(t+1). -/
theorem global_affine {runtime time : ℕ → ℕ} (bounded : ResourceOrder runtime time) :
    ∃ constant : ℕ, 0 < constant ∧ ∀ n, runtime n ≤ constant * (time n + 1) := by
  obtain ⟨a, threshold, positive, bound⟩ := bounded
  let initial := (Finset.range threshold).sup runtime
  refine ⟨a + initial + 1, by omega, ?_⟩
  intro n
  by_cases large : threshold ≤ n
  · exact (bound n large).trans (Nat.mul_le_mul (by omega) (Nat.le_succ _))
  · have small : runtime n ≤ initial :=
      Finset.le_sup (f := runtime) (Finset.mem_range.mpr (by omega))
    calc
      runtime n ≤ initial := small
      _ ≤ a + initial + 1 := by omega
      _ = (a + initial + 1) * 1 := by simp
      _ ≤ (a + initial + 1) * (time n + 1) := Nat.mul_le_mul_left _ (by omega)

theorem add {first second time : ℕ → ℕ}
    (left : ResourceOrder first time) (right : ResourceOrder second time) :
    ResourceOrder (fun n => first n + second n) time := by
  obtain ⟨a, startA, positiveA, boundA⟩ := left
  obtain ⟨b, startB, positiveB, boundB⟩ := right
  refine ⟨a + b, max startA startB, by omega, ?_⟩
  intro n large
  calc
    first n + second n ≤ a * time n + b * time n :=
      Nat.add_le_add (boundA n ((Nat.le_max_left _ _).trans large))
        (boundB n ((Nat.le_max_right _ _).trans large))
    _ = (a + b) * time n := (Nat.add_mul _ _ _).symm

/-- The ordinary-input scan is absorbed exactly under the paper's lower bound. -/
theorem identity {time : ℕ → ℕ} (dominates : ∀ n, n ≤ time n) :
    ResourceOrder (fun n => n) time :=
  ⟨1, 0, by decide, fun n _ => by simpa using dominates n⟩

end ComplexityOfGenerators.Multitape.ResourceOrder
