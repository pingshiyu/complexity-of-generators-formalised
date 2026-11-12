import ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher.Basic

namespace ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α Q S : Type} {k : ℕ} (B : TapeBank Unit Bool α Q S k)

/-- All results, including mismatches and short random tapes, are simulated
transition for transition. The fixed work bank is unchanged. -/
theorem executes (data : InputData α Bool) (bits : BitString)
    {source : BankConfiguration α Q S k} {ticks : ℕ} {result : Outcome α}
    (execution : B.Executes (sourceData data) bits source ticks result) :
    (bank B).Executes data bits (configuration data.input source) ticks (outcome data.input result) := by
  classical
  induction execution with
  | accept source table =>
      by_cases same : source.output = data.input
      · have target : (bank B).instruction data (configuration data.input source) = .accept := by
          rw [configuration_instruction B data source, table]
          simp [instruction, matcher_finished_bool, same]
        simpa [outcome, same, configuration] using TapeBank.Executes.accept (B := bank B) _ target
      · have target : (bank B).instruction data (configuration data.input source) = .reject := by
          rw [configuration_instruction B data source, table]
          simp [instruction, matcher_finished_bool, same]
        simpa [outcome, same] using TapeBank.Executes.reject (B := bank B) _ target
  | reject source table =>
      exact .reject _ (by rw [configuration_instruction B data source, table]; rfl)
  | exhausted source no yes table absent =>
      exact .exhausted _ (no, decide (source.output <+: data.input))
        (yes, decide (source.output <+: data.input))
        (by rw [configuration_instruction B data source, table]; rfl) absent
  | random source no yes bit ticks result table lookup rest ih =>
      apply TapeBank.Executes.random (B := bank B) _
        (no, decide (source.output <+: data.input))
        (yes, decide (source.output <+: data.input)) bit ticks (outcome data.input result)
        (by rw [configuration_instruction B data source, table]; rfl) lookup
      rw [configuration_choose]
      exact ih
  | step source next write work input auxiliary index emit ticks result table rest ih =>
      cases emit with
      | none =>
        apply TapeBank.Executes.step (B := bank B) _
          (next, decide (source.output <+: data.input)) write work .stay auxiliary index none
          ticks (outcome data.input result)
          (by rw [configuration_instruction B data source, table]; rfl)
        rw [configuration_step_none B data source next write work input auxiliary index]
        exact ih
      | some letter =>
        apply TapeBank.Executes.step (B := bank B) _
          (next, decide (source.output <+: data.input) &&
            decide (data.input[min source.output.length data.input.length]? = some letter))
          write work .right auxiliary index none ticks (outcome data.input result)
          (by rw [configuration_instruction B data source, table]; rfl)
        rw [configuration_step_some B data source next write work input auxiliary index letter]
        exact ih

end
end ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher
