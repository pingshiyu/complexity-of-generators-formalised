import ComplexityOfGenerators.Proofs.ExactRecursiveSupport
import ComplexityOfGenerators.Simulation.WordStack.Shortlex

/-! Polynomially clocked enumeration for the native construction. -/

namespace ComplexityOfGenerators.SelfReduction

noncomputable section

open Simulation.WordStack
variable {α : Type} [Fintype α] {L : Language α} (R : SelfReduction L)

theorem label_power_polynomial (alphabet : List α) (n : ℕ) :
    (alphabet.length + 1) ^ (R.labelWidth n + 1) ≤ R.labelCountBound alphabet n := by
  have alphabetBound : alphabet.length + 1 ≤ 2 ^ (alphabet.length + 1) := (Nat.lt_two_pow_self).le
  have logBound : 2 ^ Nat.log 2 (n + 1) ≤ n + 1 := Nat.pow_log_le_self 2 (by omega)
  calc
    (alphabet.length + 1) ^ (R.labelWidth n + 1) ≤
        (2 ^ (alphabet.length + 1)) ^ (R.labelWidth n + 1) := pow_le_pow_left' alphabetBound _
    _ = 2 ^ ((alphabet.length + 1) * (R.logConstant + 1)) *
        (2 ^ Nat.log 2 (n + 1)) ^ ((alphabet.length + 1) * R.logCoefficient) := by
      simp only [← pow_mul, ← pow_add, labelWidth]
      congr 1
      ring
    _ ≤ R.labelCountBound alphabet n := Nat.mul_le_mul_left _ (pow_le_pow_left' logBound _)

/-- All labels needed by a positive inverse edge occur before this polynomial
clock expires, even when the reduction preserves the word length. -/
theorem inverse_label_in_shortlex (alphabet : List α) (card : alphabet.length = Fintype.card α)
    (first : α) (least : Simulation.CyclicGenerator.firstLetter = some first)
    {n : ℕ} {x y w : Word α} (member : x ∈ R.inverseFibre n y w) :
    w ∈ Shortlex.labels first (R.labelCountBound alphabet n) := by
  apply Shortlex.mem_labels first least
  have positive : 0 < Fintype.card α := Fintype.card_pos_iff.mpr ⟨first⟩
  apply (Shortlex.rank_bound w positive).trans_le
  calc
    (Fintype.card α + 1) ^ (w.length + 1) ≤ (Fintype.card α + 1) ^ (R.labelWidth n + 1) := by
      apply Nat.pow_le_pow_right (by omega)
      rw [member.2.2]
      exact Nat.add_le_add_right (R.ancestor_width_le member.1) 1
    _ ≤ R.labelCountBound alphabet n := by simpa [card] using R.label_power_polynomial alphabet n

end
end ComplexityOfGenerators.SelfReduction
