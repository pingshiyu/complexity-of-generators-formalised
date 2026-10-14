import ComplexityOfGenerators.Foundations.LanguageClosure
import ComplexityOfGenerators.Simulation.DecisionComplement
import ComplexityOfGenerators.Proofs.PolynomialGenerationContainment
import ComplexityOfGenerators.Proofs.BinaryCollisionFinder

/-!
# Native complement facts and the final closure contradictions in 7.2

The fallback reduction below takes two explicit generator memberships. Their
native constructions are proved in `FallbackGeneration` and used by the
completed nonclosure proofs in `GeneratorNonclosure`.
-/

namespace ComplexityOfGenerators

theorem p_closed_under_complement {α : Type} [Fintype α] {L : Language α}
    (member : L ∈ P α) : Lᶜ ∈ P α := by
  obtain ⟨M, p, deterministic, time, language⟩ := member
  refine ⟨Simulation.decisionComplement M, p,
    Simulation.decisionComplement_deterministic M deterministic,
    fun w => Simulation.decisionComplement_timeBound M _ _ (time w), ?_⟩
  intro w
  rw [Simulation.decisionComplement_accepts_iff M deterministic _ ⟨p w.length, time w []⟩,
    language w]
  rfl

theorem pg_subset_coNP_of_complement_closed {α : Type} [Fintype α]
    (closed : ClosedUnderComplement (PG α)) : PG α ⊆ coNP α := by
  intro L member
  exact pg_subset_np (closed L member)

/-- The algebraic end of the intersection argument, applied to the native
generators constructed in `FallbackGeneration`. -/
theorem not_intersection_closed_of_fallbacks (L : Language Bool)
    (zero : L ∪ constantBitLanguage false ∈ PG Bool)
    (one : L ∪ constantBitLanguage true ∈ PG Bool) (outside : L ∉ PG Bool) :
    ¬ ClosedUnderIntersection (PG Bool) := by
  intro closed
  apply outside
  simpa only [fallback_intersection] using closed _ _ zero one

theorem HashFunction.not_intersection_closed_of_fallbacks (h : HashFunction)
    (secure : h.CollisionResistant)
    (zero : h.binaryCollisionLanguage ∪ constantBitLanguage false ∈ PG Bool)
    (one : h.binaryCollisionLanguage ∪ constantBitLanguage true ∈ PG Bool) :
    ¬ ClosedUnderIntersection (PG Bool) :=
  ComplexityOfGenerators.not_intersection_closed_of_fallbacks h.binaryCollisionLanguage zero one
    (h.binaryCollisionLanguage_not_mem_pg secure)

end ComplexityOfGenerators
