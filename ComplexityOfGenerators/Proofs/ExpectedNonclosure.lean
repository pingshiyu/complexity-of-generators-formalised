import ComplexityOfGenerators.Proofs.ExpectedGenerationContainment
import ComplexityOfGenerators.Proofs.ExpectedLengthContainment
import ComplexityOfGenerators.Proofs.ELEPGCollision
import ComplexityOfGenerators.Proofs.GeneratorNonclosure

/-!
# Non-compositionality for expected-time generator classes

The witnesses are actual native polynomial-time fallback generators. Their
intersection remains infinite. Complement nonclosure uses only the proved
NP containment and the availability of the infinite polynomial-time fillers.
-/

namespace ComplexityOfGenerators

/-- A positive constant-bit filler makes any language infinite. -/
theorem union_constantBitLanguage_infinite (L : Language Bool) (bit : Bool) :
    (L ∪ constantBitLanguage bit).Infinite := by
  apply Set.infinite_of_injective_forall_mem
    (f := fun n : ℕ => List.replicate (n + 1) bit)
  · intro n m equal
    have length := congrArg List.length equal
    simp only [List.length_replicate] at length
    omega
  · intro n
    apply Or.inr
    refine ⟨?_, ?_⟩
    · intro empty
      have length := congrArg List.length empty
      simp at length
    · intro letter member
      exact (List.mem_replicate.mp member).2

/-- The complement obstruction applies to a class between infinite PG
languages and NP; it does not require including finite languages. -/
theorem not_complement_closed_of_infinite_pg_lift (C : LanguageClass Bool)
    (lift : ∀ {L : Language Bool}, L.Infinite → L ∈ PG Bool → L ∈ C)
    (inside : C ⊆ NP Bool) (different : NP Bool ≠ coNP Bool) :
    ¬ ClosedUnderComplement C := by
  intro closed
  apply different
  apply np_eq_coNP_iff_complement_closed.mpr
  intro L member
  have zero := inside (closed _ (lift (union_constantBitLanguage_infinite L false)
    (np_union_constantBit_mem_pg member false)))
  have one := inside (closed _ (lift (union_constantBitLanguage_infinite L true)
    (np_union_constantBit_mem_pg member true)))
  have united := np_union zero one
  have equal : (L ∪ constantBitLanguage false)ᶜ ∪
      (L ∪ constantBitLanguage true)ᶜ = Lᶜ := by
    rw [← Set.compl_inter, fallback_intersection]
  exact equal ▸ united

theorem epg_not_complement_closed (different : NP Bool ≠ coNP Bool) :
    ¬ ClosedUnderComplement (EPG Bool) :=
  not_complement_closed_of_infinite_pg_lift (EPG Bool)
    (fun _ pg => pg_subset_epg pg) epg_subset_np different

/-- The current ELEPG complement obstruction uses the proved native NP
containment and the infinite-language PG conversion. -/
theorem elepg_not_complement_closed (different : NP Bool ≠ coNP Bool) :
    ¬ ClosedUnderComplement (ELEPG Bool) :=
  not_complement_closed_of_infinite_pg_lift (ELEPG Bool)
    (fun infinite pg => pg_mem_elepg_of_infinite pg infinite) elepg_subset_np different

namespace HashFunction

theorem collisionWithEmpty_not_mem_epg (h : HashFunction) (secure : h.CollisionResistant) :
    h.collisionWithEmpty ∉ EPG Bool := by
  intro expected
  exact h.collisionWithEmpty_not_mem_elepg secure
    (epg_mem_elepg_of_infinite expected h.collisionWithEmpty_infinite)

theorem collisionWithEmpty_not_mem_pg (h : HashFunction) (secure : h.CollisionResistant) :
    h.collisionWithEmpty ∉ PG Bool := by
  intro polynomial
  exact h.collisionWithEmpty_not_mem_epg secure (pg_subset_epg polynomial)

end HashFunction

theorem epg_not_intersection_closed (hashes : CollisionResistantHashFunctionsExist) :
    ¬ ClosedUnderIntersection (EPG Bool) := by
  obtain ⟨h, secure⟩ := hashes
  exact h.not_intersection_closed_of_collisionWithEmpty (EPG Bool)
    (pg_subset_epg (h.collisionFallback_mem_pg false))
    (pg_subset_epg (h.collisionFallback_mem_pg true))
    (h.collisionWithEmpty_not_mem_epg secure)

theorem epg_infinite_intersection_witness (hashes : CollisionResistantHashFunctionsExist) :
    ∃ A B : Language Bool, A ∈ EPG Bool ∧ B ∈ EPG Bool ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ EPG Bool := by
  obtain ⟨h, secure⟩ := hashes
  exact h.collisionFallbacks_infinite_intersection_witness (EPG Bool)
    (pg_subset_epg (h.collisionFallback_mem_pg false))
    (pg_subset_epg (h.collisionFallback_mem_pg true))
    (h.collisionWithEmpty_not_mem_epg secure)

theorem pg_infinite_intersection_witness (hashes : CollisionResistantHashFunctionsExist) :
    ∃ A B : Language Bool, A ∈ PG Bool ∧ B ∈ PG Bool ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ PG Bool := by
  obtain ⟨h, secure⟩ := hashes
  exact h.collisionFallbacks_infinite_intersection_witness (PG Bool)
    (h.collisionFallback_mem_pg false) (h.collisionFallback_mem_pg true)
    (h.collisionWithEmpty_not_mem_pg secure)

end ComplexityOfGenerators
