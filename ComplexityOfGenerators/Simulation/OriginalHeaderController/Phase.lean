import ComplexityOfGenerators.Simulation.OriginalHeaderController.Basic
import ComplexityOfGenerators.Simulation.BoundedMachinePhase.Canonical

namespace ComplexityOfGenerators.Simulation.OriginalHeaderController
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable (selector : Machine Unit Bool Bool) (width clock : PolynomialBound)

abbrev cap : PolynomialBound := BoundedMachinePhase.cap width clock
abbrev phaseTime : PolynomialBound := BoundedMachinePhase.time selector width clock
def reference (n : ℕ) (bits : BitString) : Option (List Bool) := UnionGenerator.sourceValue selector clock n bits

theorem phase_correct : FixedBlockRetry.PhaseCorrect (unitSymbol selector) Symbol.bit (headerBit selector)
    width (phase selector width clock) (reference selector clock) := by
  simpa only [FixedBlockRetry.PhaseCorrect,phase,Routine.mapOutput,unitSymbol,headerBit,reference] using
    BoundedMachinePhase.phase_correct selector width clock

theorem phase_bound : FixedBlockRetry.PhaseBound Symbol.bit width (cap width clock) (phaseTime selector width clock)
    (phase selector width clock) := by
  simpa only [FixedBlockRetry.PhaseBound,phase,Routine.mapOutput] using
    BoundedMachinePhase.phase_bound selector width clock

theorem phase_frame (s : Store selector) : ((phase selector width clock).eval s 22).length=(s 22).length := by
  change ((BoundedMachinePhase.phase selector width clock).eval s 22).length=(s 22).length
  exact congrArg List.length (BoundedMachinePhase.phase_fixes22 selector width clock s)

theorem phase_canonical (n : ℕ) (block : BitString) (s : Store selector)
    (length : block.length=width n) (index : (s 13).length=n) (master : (s 22).length=n)
    (random : s 17=block.map Symbol.bit) : BoundedMachinePhase.Canonical selector ((phase selector width clock).eval s) := by
  exact BoundedMachinePhase.phase_canonical selector width clock n block s length index master random

theorem restore_canonical (s : Store selector) (canonical : BoundedMachinePhase.Canonical selector s) :
    BoundedMachinePhase.Canonical selector ((FixedBlockRetry.restoreIndex (O := Event) (unitSymbol selector)).eval s) := by
  obtain ⟨word,equal⟩ := canonical
  exact ⟨word,by simpa only [FixedBlockRetry.restoreIndex,Routine.assign_eval,Function.update_of_ne (by decide :
    (31 : Fin 35)≠13),Function.update_of_ne (by decide : (31 : Fin 35)≠33)] using equal⟩

theorem ready_state (n random : ℕ) : FixedBlockRetry.State n (cap width clock n) (readyMemory selector n random) := by
  have budget : n+1≤cap width clock n := BoundedMachinePhase.indexBudget width clock n
  refine ⟨le_rfl,by simp [readyMemory,readyStore],by simp [readyMemory,readyStore],rfl,?_⟩
  intro reg
  by_cases first : reg=13 <;> by_cases second : reg=22 <;>
    simp [readyMemory,readyStore,first,second] <;> omega

end
end ComplexityOfGenerators.Simulation.OriginalHeaderController
