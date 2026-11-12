import ComplexityOfGenerators.Examples.HAMPATHNative.Inverse.Controller.Resources
import ComplexityOfGenerators.Examples.HAMPATHBaseNative

/-! Native inverse insertion with finite incident-edge coins, a bounded
position choice with valid fallback, exact fibre support, and uniform
polynomial trial time. -/

namespace ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse

noncomputable def recursiveGenerators : ExactRecursiveGenerators selfReduction where
  base := BaseSearch.base
  baseTime := BaseSearch.base_polynomialTime
  base_language := BaseSearch.base_language
  inverse := Controller.machine
  inverseSeed := seed
  inverseTime := Controller.time
  inverse_generator := by
    rintro n target label ⟨graph,start,member,rfl⟩
    exact Controller.machine_generator graph start n member label
  inverse_language := by
    rintro n target label ⟨graph,start,member,rfl⟩
    exact Controller.machine_language graph start n member label
  inverse_time := by
    rintro n target label ⟨graph,start,member,rfl⟩
    exact Controller.machine_trialBound graph start n member label

end ComplexityOfGenerators.Examples.HAMPATH.Native.Inverse
