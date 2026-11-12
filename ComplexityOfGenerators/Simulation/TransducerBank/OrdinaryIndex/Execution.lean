import ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex.Commit

namespace ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {I A O Q S : Type} {k : ℕ} (B : TapeBank I A O Q S k)

@[simp] theorem configuration_choose (data : InputData I A) (source : BankConfiguration O Q S k)
    (no yes : Q) (bit : Bool) :
    TapeBank.choose (inspecting B data source) (if bit then .fetch yes else .fetch no) =
      configuration B data (TapeBank.choose source (if bit then yes else no)) := by
  cases bit <;> rfl

/-- Simulate arbitrary source executions after real length-index preparation.
Every source step costs at most three transitions, including terminal lookup. -/
theorem executes (data : InputData I A) (bits : BitString)
    {source : BankConfiguration O Q S k} {ticks : ℕ} {result : Outcome O}
    (execution : B.Executes (sourceData data) bits source ticks result)
    (r : ℕ) (bounds : B.Bounded (sourceData data) r source) :
    ∃ targetTicks, targetTicks ≤ 3 * ticks + 1 ∧
      (bank B).Executes data bits (configuration B data source) targetTicks result := by
  induction execution generalizing r with
  | accept source action =>
      have terminal : (bank B).instruction data (inspecting B data source) = .accept := by
        rw [inspect_instruction B data source, action]
      exact ⟨1, by omega, (fetch_step B data bits r source bounds).executes (bank B)
        (.accept _ terminal)⟩
  | reject source action =>
      have terminal : (bank B).instruction data (inspecting B data source) = .reject := by
        rw [inspect_instruction B data source, action]
      exact ⟨1, by omega, (fetch_step B data bits r source bounds).executes (bank B)
        (.reject _ terminal)⟩
  | exhausted source no yes action absent =>
      have terminal : (bank B).instruction data (inspecting B data source) =
          .readRandom (.fetch no) (.fetch yes) := by
        rw [inspect_instruction B data source, action]
      exact ⟨1, by omega, (fetch_step B data bits r source bounds).executes (bank B)
        (.exhausted _ (.fetch no) (.fetch yes) terminal absent)⟩
  | random source no yes bit ticks result action lookup rest ih =>
      obtain ⟨targetTicks, cost, execution⟩ := ih (r + 1)
        (B.choose_bounded (sourceData data) r source _ bounds)
      have terminal : (bank B).instruction data (inspecting B data source) =
          .readRandom (.fetch no) (.fetch yes) := by
        rw [inspect_instruction B data source, action]
      have after : (bank B).Executes data bits (inspecting B data source)
          (targetTicks + 1) result := by
        apply TapeBank.Executes.random (B := bank B) _ (.fetch no) (.fetch yes)
          bit targetTicks result terminal lookup
        rw [configuration_choose]
        exact execution
      exact ⟨1 + (targetTicks + 1), by omega,
        (fetch_step B data bits r source bounds).executes (bank B) after⟩
  | step source next write work input auxiliary index emit ticks result action rest ih =>
      obtain ⟨targetTicks, cost, execution⟩ := ih (r + 1)
        (B.advance_bounded (sourceData data) r source
          next write work input auxiliary index emit bounds)
      have path := step_path B data bits r source bounds next write work
        input auxiliary index emit action
      exact ⟨3 + targetTicks, by omega, path.executes (bank B) execution⟩

end
end ComplexityOfGenerators.Simulation.TransducerBank.OrdinaryIndex
