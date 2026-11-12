import ComplexityOfGenerators.Simulation.BoundedHeaderCertification.Bounds
import ComplexityOfGenerators.Simulation.FixedBlockRetry.BoundedView

/-! The index-header certifier is a genuine native finite-control machine.
One full random block executes exactly one capped original-source test. -/
namespace ComplexityOfGenerators.Simulation.BoundedHeaderCertification
open WordStack
open UnionGenerator (Symbol)
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (M : Machine Unit Bool α)

noncomputable def machine (tag : Bool) (seed clock : PolynomialBound) : Machine Unit Bool Bool :=
  FixedBlockRetry.machine Symbol.unit Symbol.bit (decode M) seed (phase M tag seed clock)

def nativeClock (seed clock : PolynomialBound) : PolynomialBound :=
  FixedBlockRetry.singleClock seed (BoundedMachinePhase.cap seed clock) (BoundedMachinePhase.time M seed clock)

theorem native_view (tag : Bool) (seed clock : PolynomialBound) (n : ℕ) (bits : BitString)
    (length : bits.length=seed n) :
    UnionGenerator.sourceValue (machine M tag seed clock) (nativeClock M seed clock) n bits=
      (UnionGenerator.sourceValue M clock n bits).map (fun _ => List.replicate (n+1) tag) := by
  exact FixedBlockRetry.sourceValue_full_block Symbol.unit Symbol.bit (decode M) seed
    (BoundedMachinePhase.cap seed clock) (BoundedMachinePhase.time M seed clock) (phase M tag seed clock)
    (value M tag clock) (phase_correct M tag seed clock) (phase_bound M tag seed clock)
    (fun s => congrArg List.length (phase_fixes22 M tag seed clock s)) n bits
    (BoundedMachinePhase.indexBudget seed clock n) (BoundedMachinePhase.widthBudget seed clock n) length

end
end ComplexityOfGenerators.Simulation.BoundedHeaderCertification
