import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Native
import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Bounds
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller

open Simulation.WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] InverseNative.bodyTransform transform parse NativeSubstitution.prepareStream

noncomputable def time : PolynomialBound := InputBank.Capped.controllerTime primitiveTime

/-- The native time budget depends only on the unary family index, including
when either ordinary input word is arbitrarily longer than that index. -/
theorem machine_bounded {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active)
    (n : ℕ) (label : List Symbol) (bits : BitString) (short : bits.length ≤ seed n) :
    machine.HaltsWithin (data n (formula.encode capacity active) label) bits (time n) := by
  have bitsSize : bits.length ≤ n+1 := by simpa only [seed_eq] using short
  by_cases oversized : n < (formula.encode capacity active).length ∨ n < label.length
  · obtain ⟨ticks,cost,run⟩ := InputBank.Capped.controller_oversized_run program 0 1 (id : Symbol → Symbol) id
      (data n (formula.encode capacity active) label) bits oversized
    have seedSize := primitiveTime_seed n
    have bodySize : bits.length ≤ 4*n+2+2*primitiveTime n := by omega
    have compileBound : InputBank.Capped.compileBudget n bits.length ≤
        InputBank.Capped.controllerBudget n (primitiveTime n) := InputBank.Capped.compileBudget_mono bodySize
    have total := cost.trans (compileBound.trans (InputBank.Capped.controllerTime_bound primitiveTime n (primitiveTime n) le_rfl))
    exact machine.haltsWithin_mono _ bits total ⟨.exhausted,run⟩
  · have targetSize : (formula.encode capacity active).length ≤ n := by omega
    have labelSize : label.length ≤ n := by omega
    obtain ⟨ticks,cost,result,run,_⟩ := command_runs_canonical bound formula valid n label bits
    have primitiveCost := cost.trans (commandBudget_bound bound formula valid n label bits targetSize labelSize bitsSize)
    have execution := Program.Evaluates.executes _ (run.compiled 0 (Nat.zero_le _))
    change program.Executes n bits ((loaded (formula.encode capacity active) label).at program.initial) ticks result.outcome at execution
    rw [← loaded_eq n (formula.encode capacity active) label] at execution
    obtain ⟨nativeTicks,nativeCost,native⟩ := InputBank.Capped.run_controller_compiled program 0 1 id id (by decide)
      (data n (formula.encode capacity active) label) bits targetSize labelSize ticks result.outcome execution
    have total := nativeCost.trans (InputBank.Capped.controllerTime_bound primitiveTime n ticks primitiveCost)
    exact machine.haltsWithin_mono _ bits total ⟨result.outcome,native⟩

theorem machine_trialBound {capacity active : ℕ} (bound : active ≤ capacity)
    (formula : Formula) (valid : formula.valid active) (satisfiable : Satisfiable active formula)
    (n : ℕ) (label : List Symbol) :
    machine.GeneratorTimeBound (data n (formula.encode capacity active) label) (seed n) (time n) :=
  ⟨machine_bounded bound formula valid n label,full_trial bound formula valid satisfiable n label⟩

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative.Controller
