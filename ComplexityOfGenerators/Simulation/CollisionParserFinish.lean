import ComplexityOfGenerators.Simulation.CollisionParserYSteps

namespace ComplexityOfGenerators.Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

/-- After validation, all three read-only virtual heads are reset by explicit
scans. The work and output tapes for both hash runs are still blank. -/
theorem collisionY_finish (word x y : BitString)
    (encoding : word = collisionBits x ++ true :: false :: collisionBits y)
    (lengths : x.length = y.length) (different : x ≠ y) :
    (collisionBank M).Steps word (collisionYConfiguration M x y)
      (2 * y.length + (x.length - 1) + 4) (collisionParsedConfiguration M word x y) := by
  let B := collisionBank M
  let c := collisionYConfiguration M x y
  have length : word.length = 2 * x.length + 2 + 2 * y.length := by simp [encoding]; omega
  have bound : c.inputHead ≤ word.length := by dsimp [c, collisionYConfiguration]; omega
  have read : word[c.inputHead]? = none := by
    have pos : c.inputHead = word.length := by dsimp [c, collisionYConfiguration]; omega
    simp [pos]
  let c₀ := {c with state := CollisionPhase.resetInputs (states := M.states) (symbols := M.symbols) 0}
  let c₁ : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {c₀ with state := .resetInputs 1, head := Function.update c₀.head 0 0}
  let c₂ : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {c₁ with state := .resetInputs 2, head := Function.update c₁.head 1 0}
  let c₃ : BankConfiguration (CollisionPhase M.states M.symbols) (CollisionCell M.symbols) 7 :=
    {c₂ with state := .hashWork false M.initial, head := Function.update c₂.head 2 0}
  have action : B.instruction word c = .step (.resetInputs 0)
      (c.tape (B.select c.state) (c.head (B.select c.state))) .stay .stay := by
    dsimp [TapeBank.instruction]
    rw [read]
    simp [B, collisionBank, c, collisionYConfiguration, collisionLoadedTapes,
      collisionSelect, collisionTransition, ← lengths, different]
  have first := TapeBank.Steps.single B word c (.resetInputs 0) _ .stay .stay action
  rw [TapeBank.advance_stay B word c _ bound] at first
  have reset₀ : B.Steps word c₀ (y.length + 1) c₁ :=
    TapeBank.rewind B word (.resetInputs 0) (.resetInputs 1) 0 rfl
      (fun _ _ _ => rfl) y.length c₀ rfl (by simp [c₀, c, collisionYConfiguration]) bound
  have reset₁ : B.Steps word c₁ (y.length + 1) c₂ :=
    TapeBank.rewind B word (.resetInputs 1) (.resetInputs 2) 1 rfl
      (fun _ _ _ => rfl) y.length c₁ rfl (by simp [c₁, c₀, c, collisionYConfiguration]) bound
  have reset₂ : B.Steps word c₂ (x.length - 1 + 1) c₃ :=
    TapeBank.rewind B word (.resetInputs 2) (.hashWork false M.initial) 2 rfl
      (fun _ _ _ => rfl) (x.length - 1) c₂ rfl (by simp [c₂, c₁, c₀, c, collisionYConfiguration]) bound
  have equal : c₃ = collisionParsedConfiguration M word x y := by
    apply BankConfiguration.ext
    · rfl
    · exact length.symm
    · funext j
      simp [c₃, c₂, c₁, c₀, c, collisionYConfiguration, collisionParsedConfiguration, Function.update_apply]
      split_ifs <;> simp_all
    · rfl
  rw [equal] at reset₂
  convert ((first.trans B reset₀).trans B reset₁).trans B reset₂ using 1 <;> omega

end
end ComplexityOfGenerators.Simulation
