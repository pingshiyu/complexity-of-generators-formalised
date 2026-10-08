import ComplexityOfGenerators.Simulation.VirtualIndexSimulation
import ComplexityOfGenerators.Foundations.ResourceBounds

/-!
# Polynomial time for the complete virtual-index execution core

The source and target use the same finite random tape. Every accepted output,
explicit rejection, or exhaustion is preserved. A source execution of `t`
transitions, starting at work-head distance at most `r`, is simulated within
`(t + 1) * (2 * (r + t) + 2 * indexLength + 8)` native transitions.
The target configuration here is prepared; loading remains an explicit step.
-/

namespace ComplexityOfGenerators.Simulation

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {O : Type} [Fintype O] (M : Machine Unit Bool O)

theorem index_simulates_runFrom (data : InputData Unit Bool) (bits : BitString) (length t r : ℕ)
    (source : Configuration M) (negative : Bool) (target : Configuration (virtualIndexCore M))
    (related : IndexReady M length source negative target)
    (resources : M.ConfigurationBound (generatorData length) r source) (result : Outcome O)
    (execution : M.runFrom (generatorData length) bits source t = .halted result) :
    ∃ ticks, ticks ≤ (t + 1) * (2 * (r + t) + 2 * length + 8) ∧
      (virtualIndexCore M).runFrom data bits target ticks = .halted result := by
  induction t generalizing r source negative target with
  | zero =>
      have halted : M.observe (generatorData length) bits source = .halted result := execution
      refine ⟨source.workHead.natAbs + source.indexHead + 2, ?_,
        index_simulates_observe_halted M data bits length source negative target related result halted⟩
      have headBound := resources.workHead_natAbs M
      have indexBound : source.indexHead ≤ length := resources.indexHead
      simp only [Nat.add_zero, Nat.zero_add, Nat.one_mul]
      omega
  | succ t ih =>
      cases observation : M.observe (generatorData length) bits source with
      | halted outcome =>
          have sourceHalted := M.runFrom_halted (generatorData length) bits source outcome observation (t + 1)
          have same := RunState.halted.inj (sourceHalted.symm.trans execution)
          subst outcome
          refine ⟨source.workHead.natAbs + source.indexHead + 2, ?_,
            index_simulates_observe_halted M data bits length source negative target related result observation⟩
          have headBound := resources.workHead_natAbs M
          have indexBound : source.indexHead ≤ length := resources.indexHead
          nlinarith
      | running current =>
          have same := M.observe_running_eq (generatorData length) bits source current observation
          subst current
          obtain ⟨nextSource, sourceNext⟩ := M.next_running_of_observe_running (generatorData length) bits source observation
          have nextResources : M.ConfigurationBound (generatorData length) (r + 1) nextSource := by
            simpa only [sourceNext, Machine.ExecutionBound] using
              M.next_executionBound (generatorData length) bits r source resources
          have remaining : M.runFrom (generatorData length) bits nextSource t = .halted result := by
            rw [← M.runFrom_shift (generatorData length) bits source nextSource observation sourceNext t]
            exact execution
          obtain ⟨stepTime, nextTarget, nextNegative, stepBound, nextRelated, stepRun⟩ :=
            index_simulates_next M data bits length source nextSource negative target related resources.indexHead sourceNext
          obtain ⟨remainingTime, remainingBound, remainingRun⟩ :=
            ih (r + 1) nextSource nextNegative nextTarget nextRelated nextResources remaining
          refine ⟨stepTime + remainingTime, ?_, ?_⟩
          · have headBound := resources.workHead_natAbs M
            nlinarith
          · rw [(virtualIndexCore M).runFrom_add data bits target nextTarget stepTime stepRun]
            exact remainingRun

/-- A fixed quadratic simulation budget, with the original accepted output or
failure outcome preserved at that clock. -/
theorem index_simulates_run (data : InputData Unit Bool) (bits : BitString) (length t : ℕ)
    (target : Configuration (virtualIndexCore M))
    (related : IndexReady M length M.initialConfiguration false target) (result : Outcome O)
    (execution : M.run (generatorData length) bits t = .halted result) :
    (virtualIndexCore M).runFrom data bits target ((t + 1) * (2 * t + 2 * length + 8)) = .halted result := by
  obtain ⟨ticks, bound, simulated⟩ := index_simulates_runFrom M data bits length t 0 M.initialConfiguration false
    target related (M.initialConfiguration_bound (generatorData length)) result (by simpa using execution)
  simp only [Nat.zero_add] at bound
  have padded := (virtualIndexCore M).runFrom_halted_add data bits target ticks result simulated
    ((t + 1) * (2 * t + 2 * length + 8) - ticks)
  simpa only [Nat.add_sub_of_le bound] using padded

end

end ComplexityOfGenerators.Simulation
