import ComplexityOfGenerators.Foundations.SpaceCodeExecution
import ComplexityOfGenerators.Foundations.FiniteReachability

/-!
# Polynomial-depth search of the native space configuration graph

The search is the verified midpoint algorithm on bounded decision views. Its
recursion depth is an explicit exponent of the configuration count. This
specification does not yet supply a native implementation or a work-space bound
for the search stack.
-/

namespace ComplexityOfGenerators.Machine

set_option synthInstance.maxSize 4096

variable {I A O : Type} (M : Machine I A O)

/-- A uniform exponent for the finite configuration count, including all three
bounded read-only heads. In applications their tape lengths are input bounded. -/
def spaceConfigurationExponent (data : InputData I A) (s : ℕ) : ℕ :=
  M.states + (data.input.length + 1) + (data.auxiliary.length + 1) +
    (data.index + 1) + (2 * s + 1) + (M.symbols + 1) * (2 * s + 1)

theorem spaceCode_card_le_two_pow (data : InputData I A) (s : ℕ) :
    Fintype.card (M.SpaceCode data s) ≤ 2 ^ M.spaceConfigurationExponent data s := by
  rw [spaceCode_card]
  calc
    _ ≤ 2 ^ M.states * 2 ^ (data.input.length + 1) *
        2 ^ (data.auxiliary.length + 1) * 2 ^ (data.index + 1) *
        2 ^ (2 * s + 1) * (2 ^ (M.symbols + 1)) ^ (2 * s + 1) := by
      apply Nat.mul_le_mul
      · apply Nat.mul_le_mul
        · apply Nat.mul_le_mul
          · apply Nat.mul_le_mul
            · exact Nat.mul_le_mul Nat.lt_two_pow_self.le Nat.lt_two_pow_self.le
            · exact Nat.lt_two_pow_self.le
          · exact Nat.lt_two_pow_self.le
        · exact Nat.lt_two_pow_self.le
      · exact Nat.pow_le_pow_left Nat.lt_two_pow_self.le _
    _ = _ := by simp only [spaceConfigurationExponent, pow_add, pow_mul, Nat.mul_assoc]

theorem boundedDecisionView_card_le_two_pow (data : InputData I A) (s : ℕ) :
    Fintype.card (M.BoundedDecisionView data s) ≤ 2 ^ M.spaceConfigurationExponent data s := by
  have codes := M.boundedDecisionView_card_le data s
  rw [← M.spaceCode_card data s] at codes
  exact codes.trans (M.spaceCode_card_le_two_pow data s)

/-- Search for an accepting configuration using repeated midpoint enumeration
on finite codes. Both transitions and equality tests are effective; the code
contains no classical decision procedure for infinite tapes or reachability. -/
def spaceSearch (data : InputData I A) (s depth : ℕ) : Bool :=
  decide (∃ finish : M.SpaceCode data s,
    FiniteReachability.search (M.SpaceCodeEdge data s) depth
      (M.initialSpaceCode data s) finish = true ∧ M.spaceCodeAccepting data s finish = true)

/-- Correctness of the bounded search at any depth covering the configuration
count. The original machine may loop on some tapes: reachability still detects
exactly whether any finite random tape accepts. -/
theorem SpaceBound.spaceSearch_correct {data : InputData I A} {s : ℕ}
    (space : M.SpaceBound data s) (depth : ℕ)
    (large : M.spaceConfigurationExponent data s ≤ depth) :
    M.spaceSearch data s depth = true ↔ ∃ bits, M.Accepts data bits := by
  have cardinal : Fintype.card (M.SpaceCode data s) ≤ 2 ^ depth :=
    (M.spaceCode_card_le_two_pow data s).trans
      (Nat.pow_le_pow_right (by decide) large)
  simp only [spaceSearch, decide_eq_true_eq, FiniteReachability.search_iff_path _ depth cardinal]
  rw [M.spaceCode_acceptance_iff]
  exact (space.accepts_iff_boundedDecisionPath M).symm

end ComplexityOfGenerators.Machine
