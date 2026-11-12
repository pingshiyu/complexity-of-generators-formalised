import ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex.PrepareBasic

namespace ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

theorem loading_path (data : InputData I A) (bits : BitString) (count : ℕ) :
    count ≤ data.input.length →
      (bank B).Steps data bits (bank B).initialConfiguration count
        (preparing B count count .load) := by
  induction count with
  | zero =>
      intro _
      rw [preparing_zero]
      exact .refl _
  | succ count ih =>
      intro small
      exact (ih (by omega)).trans (bank B)
        (loading_step B data bits count (by omega))

theorem rewind_path (data : InputData I A) (bits : BitString) (loaded position : ℕ) :
    (bank B).Steps data bits (preparing B loaded position .rewind) position
      (preparing B loaded 0 .rewind) := by
  induction position with
  | zero => exact .refl _
  | succ position ih =>
      have path := (rewind_step B data bits loaded position).trans (bank B) ih
      simpa only [Nat.add_comm 1 position] using path

/-- Preparation writes actual unary marks, resets the actual ordinary-input
head, and leaves every source work tape blank. Its complete cost is 2n+2. -/
theorem prepare_path (data : InputData I A) (bits : BitString) :
    (bank B).Steps data bits (bank B).initialConfiguration (2 * data.input.length + 2)
      (configuration B data B.initialConfiguration) := by
  let n := data.input.length
  have first := loading_path B data bits n (Nat.le_refl _)
  have second : (bank B).Steps data bits (preparing B n n .load) 1
      (preparing B n n .rewind) := by
    apply TapeBank.Steps.go (bank B) data bits _ .rewind
      (Nat.le_refl _) (Nat.zero_le _) (Nat.zero_le _)
    simp [TapeBank.instruction, preparing, TapeBank.initialConfiguration, bank, n]
  have third := rewind_path B data bits n n
  have last : (bank B).Steps data bits (preparing B n 0 .rewind) 1
      (configuration B data B.initialConfiguration) := by
    rw [← preparing_ready B data]
    apply TapeBank.Steps.go (bank B) data bits _ (.fetch B.initial)
      (Nat.zero_le _) (Nat.zero_le _) (Nat.zero_le _)
    simp [TapeBank.instruction, preparing, TapeBank.initialConfiguration, bank]
  have path := ((first.trans (bank B) second).trans (bank B) third).trans (bank B) last
  have length : n + 1 + n + 1 = 2 * data.input.length + 2 := by dsimp [n]; omega
  simpa only [length] using path

end
end ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex
