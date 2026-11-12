import ComplexityOfGenerators.MainTheorems
import ComplexityOfGenerators.Proofs.PolynomialCertificateSchemes
import ComplexityOfGenerators.Proofs.CertificateSchemeGeneration
import ComplexityOfGenerators.Proofs.SpaceGeneration
import ComplexityOfGenerators.Proofs.PolynomialSpaceBase

/-!
# Historical theorem API

These aliases retain the numbering and entry points of the older bundled
manuscript. Current PLDI27 results are collected in `MainTheorems`; the numbers
below refer to the historical manuscript. The certificate-scheme equivalence
uses the retained positive binary certificate convention, whose relation to
the current paper is documented in `DEFINITION_CROSS_REFERENCE.md`.

Import this module for the historical API, or the root package for both APIs.
-/

namespace ComplexityOfGenerators

/-- **Historical Theorem 5.1 (Cryptographic Separation).**
“If collision-resistant hash functions exist, then PG ⊊ NP. In fact, P ⊈ PG.”
The assumption is the paper's unkeyed, uniform-attack collision resistance.
We specialise the word alphabet to binary for these bitstring complexity classes. -/
theorem theorem_5_1_cryptographic_separation
    (h : CollisionResistantHashFunctionsExist) :
    PG Bool ⊂ NP Bool ∧ ¬ P Bool ⊆ PG Bool :=
  corollary_collision_resistance_separates_polynomial_generation h

/-- **Historical Theorem 6.1.** “PSPACEG = PSPACE.”
This theorem is unrelativised, exactly as stated. Oracle equality is Proposition
6.5, not another main theorem; no oracle or cryptographic assumption is added. -/
theorem theorem_6_1_polynomial_space_generation
    (α : Type) [Fintype α] : PSPACEG α = PSPACE α := by
  apply Set.Subset.antisymm
  · exact pspaceg_subset_pspace
  · exact pspace_subset_pspaceg

/-- Historical Theorem 7.1: polynomial exact generators are certificate
schemes under the retained positive binary certificate convention. Empty
instances are allowed. The bridge to the current paper's certificate alphabet
and empty certificates is recorded in `DEFINITION_CROSS_REFERENCE.md`. -/
theorem theorem_7_1_generators_are_certificate_schemes
    {α : Type} [Fintype α] (L : Language α) :
    L ∈ PG α ↔ ∃ V : PolynomialVerifier L, HasCertificateScheme V := by
  constructor
  · exact pg_has_certificateScheme
  · rintro ⟨V, scheme⟩
    exact hasCertificateScheme_mem_pg scheme

/-- **Historical Theorem 7.2 (PG special case of current Theorem 6.1).**
“If NP ≠ coNP, then PG is not closed under complementation. If collision-resistant
hash functions exist, then PG is not closed under intersection.”
The two clauses have independent assumptions; neither is required for the other.
Closure is extensional language closure, as in the theorem's textual statement. -/
theorem theorem_7_2_efficient_generators_are_not_composable :
    (NP Bool ≠ coNP Bool → ¬ ClosedUnderComplement (PG Bool)) ∧
    (CollisionResistantHashFunctionsExist → ¬ ClosedUnderIntersection (PG Bool)) :=
  ⟨pg_not_complement_closed, pg_not_intersection_closed⟩

/-- **Historical Proposition A.23.2 (current Proposition 6.2).**
If `L` is exactly recursively generable, then `L ∈ PG`.
The construction uses the corrected optional stopping rule for reductions
that preserve word length. Its finite native machine and polynomial running
time are proved, including empty slices and the empty alphabet. -/
theorem proposition_a23_2_exact_recursive_generation
    {α : Type} [Fintype α] (L : Language α)
    (h : ExactlyRecursivelyGenerable L) : L ∈ PG α :=
  proposition_6_2_exact_recursive_generation h

/-- Expected-length extension of collision non-generability, using the same
native machine model and unkeyed uniform collision-resistance assumption.
No variance or concentration hypothesis is imposed. -/
theorem theorem_expected_length_collision_non_generability
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.binaryCollisionLanguage ∉ ELEPG Bool :=
  theorem_5_2_collision_non_generability h secure

/-- ELEPG generators are not closed under intersection if collision-resistant
hashes exist. The reduction constructs an actual polynomial-time attacker. -/
theorem theorem_expected_length_generators_are_not_composable
    (hashes : CollisionResistantHashFunctionsExist) :
    ¬ ClosedUnderIntersection (ELEPG Bool) :=
  elepg_not_intersection_closed hashes

/-- The nonclosure witness has an infinite intersection, independently of the
convention excluding finite languages from ELEPG. -/
theorem theorem_expected_length_infinite_intersection_nonclosure
    (hashes : CollisionResistantHashFunctionsExist) :
    ∃ A B : Language Bool, A ∈ ELEPG Bool ∧ B ∈ ELEPG Bool ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ ELEPG Bool :=
  elepg_infinite_intersection_witness hashes

end ComplexityOfGenerators
