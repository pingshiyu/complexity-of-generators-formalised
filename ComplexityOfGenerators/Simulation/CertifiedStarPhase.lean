import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Support
import ComplexityOfGenerators.Simulation.CertifiedStarPhase.Witnesses
import ComplexityOfGenerators.Simulation.CertifiedStarPhase.ResourceBounds
import ComplexityOfGenerators.Simulation.CertifiedStarPhase.RandomFree

/-! A concrete bounded native phase that certifies productive source indices
and selects a positive composition. It supplies PhaseCorrect, PhaseBound,
master-length preservation and RandomFree for the outer fixed-block retry
controller. Its payload is a path word; physical source output is untouched. -/
