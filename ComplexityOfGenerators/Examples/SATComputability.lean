import ComplexityOfGenerators.Examples.SATSelfReduction
import ComplexityOfGenerators.Examples.SATHeaderMachines

/-! The native rank and width transducers for padded SAT.
`SATNative.PolynomialReduction` assembles these functions with the completed
native verifier and checked substitution machine into a genuine
`PolynomialSelfReduction`. The exact inverse generator is assembled separately
with the complete native base sampler; no unfinished instance is assumed. -/

namespace ComplexityOfGenerators.Examples.PaddedCNF

def rank_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => List.replicate (selfReduction.rank word) ()) :=
  headerRank_computable

def width_computable : PolynomialWordFunction
    (fun (word : List Symbol) (_ : List Unit) => List.replicate (selfReduction.width word) ()) :=
  headerWidth_computable

end ComplexityOfGenerators.Examples.PaddedCNF
