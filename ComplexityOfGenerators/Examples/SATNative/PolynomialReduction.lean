import ComplexityOfGenerators.Examples.SATComputability
import ComplexityOfGenerators.Examples.SATNative.VerifierMachine
import ComplexityOfGenerators.Examples.SATNative.SubstitutionMachine

namespace ComplexityOfGenerators.Examples.PaddedCNF

/-- All computational fields of the padded-CNF self-reduction are actual
native deterministic polynomial machines. The exact generator family is
assembled separately from the base and inverse constructors. -/
noncomputable def polynomialSelfReduction : PolynomialSelfReduction selfReduction where
  verifier := NativeEvaluation.NativeVerifier.machine
  verifier_deterministic := NativeEvaluation.NativeVerifier.machine_deterministic
  verifierTime := NativeEvaluation.NativeVerifier.time
  verifier_time := NativeEvaluation.NativeVerifier.machine_time
  verifier_correct := by
    intro word certificate
    exact NativeEvaluation.NativeVerifier.machine_correct word certificate
  rank_computable := rank_computable
  width_computable := width_computable
  reduction_computable := NativeSubstitution.NativeReduction.computable

end ComplexityOfGenerators.Examples.PaddedCNF
