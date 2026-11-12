import ComplexityOfGenerators.Simulation.OriginalHeaderController.Native
import ComplexityOfGenerators.Simulation.OriginalBinarySelector.Properties
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Basic
import ComplexityOfGenerators.Proofs.OriginalSourceHookTrace
import ComplexityOfGenerators.Proofs.ExpectedOriginalBinarySampling

/-! Bounded native certificates select a source tag or a split; fresh original
source calls produce the output on the shared native output tape. -/
namespace ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
noncomputable section
variable {α : Type} [Fintype α] (families : Bool → UniformGenerators α) (p : PolynomialBound)
    (operation : OriginalBinarySelector.Operation)

abbrev Operation := OriginalBinarySelector.Operation
abbrev Event := OriginalHeaderController.Event
abbrev Request := OriginalHeaderController.Request

def selector : Machine Unit Bool Bool :=
  OriginalBinarySelector.machine (families false).machine (families true).machine p operation
abbrev width : PolynomialBound := ExpectedOriginalBinarySampling.width p operation
def selectorClock : PolynomialBound :=
  OriginalBinarySelector.clock (families false).machine (families true).machine p operation

def controller : Machine Unit Bool Event :=
  OriginalHeaderController.machine (selector families p operation) (width p operation)
    (selectorClock families p operation) operation

def controllerParameter := OriginalHeaderController.parameter (selector families p operation)
  (width p operation) (selectorClock families p operation) operation

def coefficient : PolynomialBound := OriginalHeaderController.primitiveCoefficient
  (selector families p operation) (width p operation) (selectorClock families p operation)

def machine : Machine Unit Bool α := NativeSourceCall.Hook.machine
  (controller families p operation) (OriginalSourceFamilySampler.source families)
  (controllerParameter families p operation) (OriginalSourceFamilySampler.entry families Prod.fst)

def reference : ℕ → BitString → Option (List Bool) :=
  OriginalHeaderController.reference (selector families p operation) (selectorClock families p operation)

abbrev selection : ℕ → BitString → Option (List Request) :=
  ExpectedOriginalBinarySampling.selection families p operation

def headerOf (n : ℕ) (requests : List Request) : List Bool :=
  match operation with
  | .union => OriginalCertification.HeaderBridge.header (requests.headD (false,0)).1 n
  | .concatenation => OriginalCertification.HeaderBridge.concatHeader n (requests.headD (false,0)).2

end
end ComplexityOfGenerators.Simulation.OriginalBinaryGenerator
