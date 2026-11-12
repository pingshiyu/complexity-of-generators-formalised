import ComplexityOfGenerators.Simulation.ExpectedOriginalStarController.Native
import ComplexityOfGenerators.Simulation.NativeSourceCall.Hook.Basic
import ComplexityOfGenerators.Simulation.NativeChoice.Basic

/-! The star generator combines the bounded certified-path controller with
original source calls. Its single output tape receives source words directly. -/
namespace ComplexityOfGenerators.Simulation.OriginalStarGenerator
noncomputable section
variable {α : Type} [Fintype α] (M : Machine Unit Bool α) (p : PolynomialBound)

noncomputable def machine : Machine Unit Bool α :=
  NativeSourceCall.Hook.machine (ExpectedOriginalStarController.machine M p)
    (NativeChoice.machine (fun _ : Bool=>M) false) (ExpectedOriginalStarController.parameter M p)
    (fun _=>NativeChoice.start (fun _ : Bool=>M) false)

end
end ComplexityOfGenerators.Simulation.OriginalStarGenerator
