import ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher.Semantics
import ComplexityOfGenerators.Simulation.TransducerBank.FixedRegionExecution
import ComplexityOfGenerators.Simulation.TransducerBank.RegionBounds

namespace ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α Q S : Type} {k : ℕ} (B : TapeBank Unit Bool α Q S k)

theorem configuration_bounded (data : InputData α Bool) (radius : ℕ) (source : BankConfiguration α Q S k)
    (bounded : B.Bounded (sourceData data) radius source) :
    (bank B).Bounded data radius (configuration data.input source) :=
  ⟨Nat.min_le_right _ _,bounded.auxiliary,bounded.index,bounded.head⟩

theorem regionSteps (data : InputData α Bool) (bits : BitString) (radius : ℕ)
    {source finish : BankConfiguration α Q S k} {ticks : ℕ}
    (path : B.RegionSteps (sourceData data) bits radius source ticks finish) :
    (bank B).RegionSteps data bits radius (configuration data.input source) ticks (configuration data.input finish) := by
  classical
  induction path with
  | refl source bounded => exact .refl _ (configuration_bounded B data radius source bounded)
  | random source no yes bit ticks finish bounded table lookup rest ih =>
    apply TapeBank.RegionSteps.random _ (no,decide (source.output <+: data.input))
      (yes,decide (source.output <+: data.input)) bit ticks _ (configuration_bounded B data radius source bounded)
      (by rw [configuration_instruction B data source,table];rfl) lookup
    rw [configuration_choose]
    exact ih
  | step source next write work input auxiliary index emit ticks finish bounded table rest ih =>
    cases emit with
    | none =>
      apply TapeBank.RegionSteps.step _ (next,decide (source.output <+: data.input)) write work .stay auxiliary index none
        ticks _ (configuration_bounded B data radius source bounded) (by rw [configuration_instruction B data source,table];rfl)
      rw [configuration_step_none]
      exact ih
    | some letter =>
      apply TapeBank.RegionSteps.step _
        (next,decide (source.output <+: data.input) && decide (data.input[min source.output.length data.input.length]?=some letter))
        write work .right auxiliary index none ticks _ (configuration_bounded B data radius source bounded)
        (by rw [configuration_instruction B data source,table];rfl)
      rw [configuration_step_some]
      exact ih

theorem regionRun (data : InputData α Bool) (bits : BitString) (radius : ℕ)
    {source : BankConfiguration α Q S k} {result : Outcome α}
    (run : B.RegionRun (sourceData data) bits radius source result) :
    (bank B).RegionRun data bits radius (configuration data.input source) (outcome data.input result) := by
  obtain ⟨ticks,finish,path,halt⟩ := run
  exact ⟨ticks,configuration data.input finish,regionSteps B data bits radius path,executes B data bits halt⟩

variable (M : MultitapeMachine Unit Bool α)

/-- Streaming output comparison preserves the actual work-head radius on all
finite choice tapes, independently of runtime or generated output length. -/
theorem spaceBound (data : InputData α Bool) (radius : ℕ)
    (terminates : M.Terminates (sourceData data)) (bounded : M.SpaceBound (sourceData data) radius) :
    (machine M).SpaceBound data radius := by
  change (bank M.program).SpaceBound data radius
  apply TapeBank.spaceBound_of_regionRuns
  intro bits
  obtain ⟨ticks,result,execution⟩ := terminates bits
  have sourceRun := execution.regionRun_of_prefixBound M.program
    (fun time finish path => bounded bits time finish path)
  refine ⟨outcome data.input result,?_⟩
  simpa only [configuration_initial] using regionRun M.program data bits radius sourceRun

end
end ComplexityOfGenerators.Simulation.TransducerBank.OutputMatcher
