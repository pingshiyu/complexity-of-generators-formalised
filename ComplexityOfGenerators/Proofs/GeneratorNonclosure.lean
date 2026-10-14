import ComplexityOfGenerators.Proofs.FallbackGeneration
import ComplexityOfGenerators.Proofs.NondeterministicUnion
import ComplexityOfGenerators.Proofs.ClosureArguments
import ComplexityOfGenerators.Proofs.PolynomialCollisionDecision

/-!
# The two independent nonclosure statements of Theorem 7.2

For every native NP language L, both L ∪ 0⁺ and L ∪ 1⁺ belong to native PG.
Their intersection is L. Complement closure of PG would consequently put
Lᶜ in NP by binary union closure, giving NP = coNP. Intersection closure would
put the secure collision language in PG, contradicting the proved reduction.
-/

namespace ComplexityOfGenerators

theorem pg_not_complement_closed (different : NP Bool ≠ coNP Bool) :
    ¬ ClosedUnderComplement (PG Bool) := by
  intro closed
  apply different
  apply np_eq_coNP_iff_complement_closed.mpr
  intro L member
  have zero := pg_subset_np (closed _ (np_union_constantBit_mem_pg member false))
  have one := pg_subset_np (closed _ (np_union_constantBit_mem_pg member true))
  have united := np_union zero one
  have equal : (L ∪ constantBitLanguage false)ᶜ ∪ (L ∪ constantBitLanguage true)ᶜ = Lᶜ := by
    rw [← Set.compl_inter, fallback_intersection]
  exact equal ▸ united

theorem pg_not_intersection_closed (hashes : CollisionResistantHashFunctionsExist) :
    ¬ ClosedUnderIntersection (PG Bool) := by
  obtain ⟨hash, secure⟩ := hashes
  have decidable := p_subset_np hash.binaryCollisionLanguage_mem_p
  exact hash.not_intersection_closed_of_fallbacks secure
    (np_union_constantBit_mem_pg decidable false)
    (np_union_constantBit_mem_pg decidable true)

end ComplexityOfGenerators
