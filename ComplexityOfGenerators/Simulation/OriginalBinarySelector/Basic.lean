import ComplexityOfGenerators.Simulation.BoundedHeaderCertification.Native
import ComplexityOfGenerators.Simulation.OriginalBinarySelector.Operation
import ComplexityOfGenerators.Proofs.BoundedCommandPhase
import ComplexityOfGenerators.Simulation.UnionGenerator.Execution
import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Execution
import ComplexityOfGenerators.Proofs.OriginalCertification.Union
import ComplexityOfGenerators.Proofs.OriginalCertification.Concatenation

/-! Native bounded selectors reuse the existing union and all-splits programs.
Only their capped source interfaces change: certificates return source-index
headers, and original source outputs are generated after selection. -/
namespace ComplexityOfGenerators.Simulation.OriginalBinarySelector
open WordStack
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {α : Type} [Fintype α] (G H : Machine Unit Bool α) (p : PolynomialBound)

def certificate (M : Machine Unit Bool α) (tag : Bool) : Machine Unit Bool Bool :=
  BoundedHeaderCertification.machine M tag (OriginalCertification.seed p) (OriginalCertification.clock p)
def certificateClock (M : Machine Unit Bool α) : PolynomialBound :=
  BoundedHeaderCertification.nativeClock M (OriginalCertification.seed p) (OriginalCertification.clock p)

abbrev Cell := UnionGenerator.Cell (certificate p G false) (certificate p H true)

def width : Operation → PolynomialBound
  | .union => OriginalCertification.Union.width p
  | .concatenation => OriginalCertification.Concatenation.width p

noncomputable def code : (operation : Operation) → Command (Cell G H p) Bool 35
  | .union => UnionGenerator.command (certificate p G false) (certificate p H true)
      (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
      (width p .union)
  | .concatenation => ConcatenationGenerator.command (certificate p G false) (certificate p H true)
      (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
      (width p .concatenation)
attribute [irreducible] code

noncomputable def stackClock : Operation → PolynomialBound
  | .union => UnionGenerator.stackTime (certificate p G false) (certificate p H true)
      (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
      (width p .union)
  | .concatenation => ConcatenationGenerator.stackTime (certificate p G false) (certificate p H true)
      (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
      (width p .concatenation)

def referenceValue (operation : Operation) (n : ℕ) (bits : BitString) : Option (List Bool) :=
  if width p operation n≤bits.length then
    match operation with
    | .union => UnionGenerator.value (certificate p G false) (certificate p H true)
        (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
        n (bits.take (width p operation n))
    | .concatenation => ConcatenationGenerator.algorithm (certificate p G false) (certificate p H true)
        (OriginalCertification.seed p) (certificateClock p G) (OriginalCertification.seed p) (certificateClock p H)
        n (bits.take (width p operation n))
  else none

noncomputable def machine (operation : Operation) : Machine Unit Bool Bool :=
  ((code G H p operation).program 0).machine

def clock (operation : Operation) : PolynomialBound := Program.compiledTime (stackClock G H p operation)

end
end ComplexityOfGenerators.Simulation.OriginalBinarySelector
