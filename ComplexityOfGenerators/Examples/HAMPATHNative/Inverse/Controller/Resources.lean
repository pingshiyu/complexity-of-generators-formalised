import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Bounds
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller

open Simulation.WordStack

set_option backward.isDefEq.respectTransparency true
attribute [local irreducible] primitiveTime

noncomputable def time : PolynomialBound := InputBank.Capped.controllerTime primitiveTime
attribute [local irreducible] time

/-- The bound is uniform in both ordinary arguments, even when either word
is arbitrarily longer than the unary family index. -/
theorem machine_bounded (graph : Graph) (start n : ℕ) (label : List Symbol) (bits : BitString)
    (inside : start<graph.size) (short : bits.length≤seed n) :
    machine.HaltsWithin (data n (graph.encode start) label) bits (time n) := by
  unfold time
  by_cases oversized : n<(graph.encode start).length ∨ n<label.length
  · obtain ⟨ticks,cost,run⟩ := InputBank.Capped.controller_oversized_run program 0 1 (id : Symbol→Symbol) id
      (data n (graph.encode start) label) bits oversized
    have seedSize := primitiveTime_seed n
    have bodySize : bits.length≤4*n+2+2*primitiveTime n := by omega
    have compileBound : InputBank.Capped.compileBudget n bits.length≤
        InputBank.Capped.controllerBudget n (primitiveTime n) := InputBank.Capped.compileBudget_mono bodySize
    have total := cost.trans (compileBound.trans (InputBank.Capped.controllerTime_bound primitiveTime n (primitiveTime n) le_rfl))
    exact machine.haltsWithin_mono _ bits total ⟨.exhausted,run⟩
  · have targetSize : (graph.encode start).length≤n := by omega
    have labelSize : label.length≤n := by omega
    obtain ⟨ticks,cost,result,run,_⟩ := command_runs graph start n label bits inside
    have primitiveCost := cost.trans ((commandBudget_bound graph start n label bits inside targetSize labelSize short).trans (primitiveBudget_le n))
    have execution := Program.Evaluates.executes _ (run.compiled 63 (Nat.zero_le _))
    change program.Executes n bits ((loaded (graph.encode start) label).at program.initial) ticks result.outcome at execution
    rw [← loaded_eq n (graph.encode start) label] at execution
    obtain ⟨nativeTicks,nativeCost,native⟩ := InputBank.Capped.run_controller_compiled program 0 1 id id (by decide)
      (data n (graph.encode start) label) bits targetSize labelSize ticks result.outcome execution
    have total := nativeCost.trans (InputBank.Capped.controllerTime_bound primitiveTime n ticks primitiveCost)
    exact machine.haltsWithin_mono _ bits total ⟨result.outcome,native⟩

theorem machine_trialBound (graph : Graph) (start n : ℕ) (member : HamiltonianFrom graph start) (label : List Symbol) :
    machine.GeneratorTimeBound (data n (graph.encode start) label) (seed n) (time n) :=
  ⟨fun bits short => machine_bounded graph start n label bits member.start_bound short,
    full_trial graph start n member label⟩

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse.Controller
