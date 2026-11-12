import ComplexityOfGenerators.Examples.SATNative.InverseNative.Controller.Resources
import ComplexityOfGenerators.Examples.SATNative.BaseSampler

/-! The concrete SAT inverse uses a native capped-input controller and a
fixed finite block of mask coins. Both exact fibre support and uniform
polynomial trial time are proved for every satisfying target and every label. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF.InverseNative

noncomputable section

/-- Both computational generator fields of exact recursive generability are
actual native machines, with no assumed inverse implementation. -/
noncomputable def recursiveGenerators : ExactRecursiveGenerators selfReduction where
  base := BaseSampler.baseFamily.toUniformGenerators
  baseTime := BaseSampler.baseFamily_polynomialTime
  base_language := BaseSampler.baseFamily_language
  inverse := Controller.machine
  inverseSeed := Controller.seed
  inverseTime := Controller.time
  inverse_generator := by
    rintro n target label ⟨capacity,active,formula,bound,valid,satisfiable,rfl⟩
    exact Controller.machine_generator bound formula valid satisfiable n label
  inverse_language := by
    rintro n target label ⟨capacity,active,formula,bound,valid,satisfiable,rfl⟩
    exact Controller.machine_language bound formula valid satisfiable n label
  inverse_time := by
    rintro n target label ⟨capacity,active,formula,bound,valid,satisfiable,rfl⟩
    exact Controller.machine_trialBound bound formula valid satisfiable n label

end
end ComplexityOfGenerators.Examples.PaddedCNF.InverseNative
