import ComplexityOfGenerators.ComplexityClasses
import ComplexityOfGenerators.Foundations.BasicTheorems

/-!
# Explicit obligations between machine models

The local model and Complexitylib use different input, output, random-choice and
space conventions. These interfaces state the comparison work still required;
they are NOT populated by an assumed instance or an unfinished proof. Main
theorem statements keep their existing meanings.

Classical theorems in `Standard` are unconditional and kernel checked. Transport
to local classes is conditional on a proved model comparison. Keeping that
condition visible avoids treating imported theorems as theorems about a different
machine model.
-/

namespace ComplexityOfGenerators

/-- A future simulation construction must establish both inclusions for each
class. This is a specification, not a claim that the comparison is proved. -/
structure DecisionClassAgreement where
  polynomialTime : P Bool = Standard.P
  nondeterministicPolynomialTime : NP Bool = Standard.NP
  polynomialSpace : PSPACE Bool = Standard.PSPACE

namespace DecisionClassAgreement

theorem p_subset_np (bridge : DecisionClassAgreement) : P Bool ⊆ NP Bool := by
  rw [bridge.polynomialTime, bridge.nondeterministicPolynomialTime]
  exact Standard.p_subset_np

theorem co_np_agreement (bridge : DecisionClassAgreement) : coNP Bool = Standard.coNP := by
  ext K
  change (Kᶜ ∈ NP Bool) ↔ Kᶜ ∈ Standard.NP
  rw [bridge.nondeterministicPolynomialTime]

end DecisionClassAgreement

/-- The two generator simulations needed to use imported Savitch:
generation to nondeterministic recognition, and decision to generation.
The fields are construction goals, not global axioms. -/
structure SpaceGenerationBridge where
  generationToRecognition : PSPACEG Bool ⊆ Standard.NPSPACE
  decisionToGeneration : Standard.PSPACE ⊆ PSPACEG Bool

theorem polynomial_space_generation_of_bridges (decision : DecisionClassAgreement)
    (generation : SpaceGenerationBridge) : PSPACEG Bool = PSPACE Bool := by
  rw [decision.polynomialSpace]
  exact Set.Subset.antisymm
    (generation.generationToRecognition.trans Standard.savitch)
    generation.decisionToGeneration

/-- The generator-specific premises left in the complement argument. Cook–Levin
and the NP/coNP collapse are supplied by the imported library, not by these fields. -/
structure PolynomialGenerationBridge where
  generationToRecognition : PG Bool ⊆ Standard.NP
  satGeneration : Standard.SAT ∈ PG Bool

theorem no_complement_closure_of_bridge (bridge : PolynomialGenerationBridge)
    (separation : Standard.NP ≠ Standard.coNP) :
    ¬ (∀ K, K ∈ PG Bool → Kᶜ ∈ PG Bool) := by
  intro closed
  exact Standard.unsat_not_mem_np separation
    (bridge.generationToRecognition (closed Standard.SAT bridge.satGeneration))

end ComplexityOfGenerators
