import ComplexityOfGenerators.Examples.HAMPATHNative.Verifier.Machine
import ComplexityOfGenerators.Examples.HAMPATHNative.RankComputability
import ComplexityOfGenerators.Examples.HAMPATHNative.WidthComputability
import ComplexityOfGenerators.Examples.HAMPATHNative.Reduction.Computability

namespace ComplexityOfGenerators.Examples.HAMPATH

/-- Each computational field of the concrete graph self-reduction is an
actual native deterministic polynomial machine. -/
noncomputable def polynomialSelfReduction : PolynomialSelfReduction selfReduction where
  verifier := Native.Verifier.machine
  verifier_deterministic := Native.Verifier.machine_deterministic
  verifierTime := Native.Verifier.time
  verifier_time := Native.Verifier.machine_time
  verifier_correct := Native.Verifier.machine_correct
  rank_computable := Native.rank_computable
  width_computable := Native.width_computable
  reduction_computable := Native.Reduction.computable

end ComplexityOfGenerators.Examples.HAMPATH
