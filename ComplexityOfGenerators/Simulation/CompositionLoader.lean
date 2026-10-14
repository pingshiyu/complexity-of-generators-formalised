import ComplexityOfGenerators.Simulation.CompositionMemory
import ComplexityOfGenerators.Simulation.TransducerBank.Rewind

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} (S : Machine Unit Bool Bool) (R : Machine Unit Bool α)

@[simp] theorem compositionIndex_zero : compositionIndex S R 0 = fun _ => {} := by
  funext i
  have empty : ¬(0 ≤ i ∧ i < (0 : ℤ)) := by omega
  simp [compositionIndex, empty]

theorem compositionIndex_succ (n : ℕ) :
    Function.update (compositionIndex S R n) (n : ℤ) {index := true} = compositionIndex S R (n + 1) := by
  funext i
  by_cases equal : i = (n : ℤ)
  · subst i
    simp [compositionIndex]
  · rw [Function.update_of_ne equal]
    have same : (0 ≤ i ∧ i < (n : ℤ)) ↔ (0 ≤ i ∧ i < ((n + 1 : ℕ) : ℤ)) := by omega
    simp [compositionIndex, same]

def compositionLoadConfiguration (n : ℕ) : CompositionConfiguration S R :=
  {samplerBankConfiguration S R n S.initialConfiguration with
    state := .load
    head := fun j => if j = 1 then (n : ℤ) else 0}

theorem composition_load_step (n k : ℕ) (bits : BitString) (available : k < n) :
    (samplerCompositionBank S R).Steps (generatorData n) bits (compositionLoadConfiguration S R k) 1
      (compositionLoadConfiguration S R (k + 1)) := by
  let B := samplerCompositionBank S R
  let c := compositionLoadConfiguration S R k
  have table : B.instruction (generatorData n) c =
      .step .load {index := true} .right .stay .stay .right none := by
    simp [B, c, TransducerBank.TapeBank.instruction, samplerCompositionBank, compositionLoadConfiguration,
      samplerBankConfiguration, compositionSelect, compositionTransition, compositionIndex, generatorData, available]
  have step := TransducerBank.TapeBank.Steps.single B (generatorData n) bits c _ _ _ _ _ _ _ table
  convert step using 1
  symm
  apply TransducerBank.BankConfiguration.ext
  · rfl
  · rfl
  · rfl
  · simp [c, compositionLoadConfiguration, samplerBankConfiguration, TransducerBank.TapeBank.advance,
      Move.onInput, generatorData, Nat.min_eq_left (show k + 1 ≤ n by omega)]
  · rfl
  · rfl
  · funext j
    fin_cases j <;> simp [B, c, compositionLoadConfiguration, TransducerBank.TapeBank.advance,
      samplerCompositionBank, compositionSelect, Move.onInt]
  · funext j i
    fin_cases j <;> simp [B, c, compositionLoadConfiguration, samplerBankConfiguration,
      TransducerBank.TapeBank.advance, samplerCompositionBank, compositionSelect,
      Machine.initialConfiguration, ← compositionIndex_succ S R, Function.update_apply]

theorem composition_load_steps (n : ℕ) (bits : BitString) (k : ℕ) (bound : k ≤ n) :
    (samplerCompositionBank S R).Steps (generatorData n) bits (compositionLoadConfiguration S R 0) k
      (compositionLoadConfiguration S R k) := by
  induction k with
  | zero => exact .refl _
  | succ k ih =>
      exact (ih (by omega)).trans _ (composition_load_step S R n k bits (by omega))

/-- Initialization builds and rewinds a genuine unary tape using `2n+2`
finite-bank instructions. The source sampler's work tape remains blank. -/
theorem composition_loaded (n : ℕ) (bits : BitString) :
    (samplerCompositionBank S R).Steps (generatorData n) bits (samplerCompositionBank S R).initialConfiguration
      (2 * n + 2) (samplerBankConfiguration S R n S.initialConfiguration) := by
  let B := samplerCompositionBank S R
  let loaded := compositionLoadConfiguration S R n
  let rewind : CompositionConfiguration S R := {loaded with state := .rewindLoad}
  have initial : B.initialConfiguration = compositionLoadConfiguration S R 0 := by
    apply TransducerBank.BankConfiguration.ext <;>
      simp [B, TransducerBank.TapeBank.initialConfiguration, samplerCompositionBank, compositionLoadConfiguration,
        samplerBankConfiguration, Machine.initialConfiguration]
  have lead := composition_load_steps S R n bits n le_rfl
  have enter : B.Steps (generatorData n) bits loaded 1 rewind := by
    apply TransducerBank.TapeBank.Steps.go <;>
      simp [B, loaded, TransducerBank.TapeBank.instruction, samplerCompositionBank, compositionLoadConfiguration,
        samplerBankConfiguration, compositionSelect, compositionTransition, generatorData]
  have reset := TransducerBank.TapeBank.rewind_steps B (generatorData n) bits .rewindLoad (.sample S.initial) 1
    rfl (by intro input auxiliary index origin cell; cases origin <;> rfl) n rewind rfl
    (by simp [rewind, loaded, compositionLoadConfiguration]) (Nat.zero_le _) (Nat.zero_le _) le_rfl
  have finished : {rewind with state := .sample S.initial, head := Function.update rewind.head 1 0} =
      samplerBankConfiguration S R n S.initialConfiguration := by
    apply TransducerBank.BankConfiguration.ext
    all_goals try rfl
    · funext j
      fin_cases j <;> simp [rewind, loaded, compositionLoadConfiguration, samplerBankConfiguration, Machine.initialConfiguration]
  rw [finished] at reset
  rw [initial]
  convert (lead.trans B enter).trans B reset using 1 <;> omega

end
end ComplexityOfGenerators.Simulation
