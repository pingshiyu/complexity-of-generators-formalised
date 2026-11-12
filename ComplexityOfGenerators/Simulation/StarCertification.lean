import ComplexityOfGenerators.Simulation.StarCertification.Support
import ComplexityOfGenerators.Simulation.StarCertification.ResourceBounds
import ComplexityOfGenerators.Simulation.StarCertification.RandomFree

/-! The native certification scan tests source indices1 through n using
consecutive bounded blocks, returns ascending cached availability flags, and
preserves the master unary target in22. Its semantics, true-flag soundness,
polynomial primitive resources and absence of nested random requests are
proved for the concrete finite stack controller. -/
