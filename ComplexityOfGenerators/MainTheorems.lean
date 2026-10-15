import ComplexityOfGenerators.Cryptography
import ComplexityOfGenerators.Certificates
import ComplexityOfGenerators.Proofs.GenerabilityContainment
import ComplexityOfGenerators.Proofs.RecognizabilityContainment
import ComplexityOfGenerators.Proofs.PolynomialGenerationContainment
import ComplexityOfGenerators.Proofs.BinaryCollisionFinder
import ComplexityOfGenerators.Proofs.PolynomialCollisionDecision
import ComplexityOfGenerators.Foundations.LanguageClosure
import ComplexityOfGenerators.Proofs.PolynomialCertificateSchemes
import ComplexityOfGenerators.Proofs.CertificateSchemeGeneration
import ComplexityOfGenerators.Proofs.GeneratorNonclosure
import ComplexityOfGenerators.Proofs.SpaceGeneration
import ComplexityOfGenerators.Proofs.PolynomialSpaceBase

/-!
# Every result marked “Theorem” in the supplied paper

Source: `complexity-of-generators-formalisation.pdf`, *Complexity Theory of
Randomised Testing*. There are five numbered theorems. Each docstring below
quotes its mathematical statement and identifies its printed page number.

All five main theorems are proved in the retained finite-control machine model.
Theorem 6.1 uses native Savitch configuration-graph search in the forward
direction and the native cyclic generator in the reverse direction. Verified
complexity proofs are in `Simulation` and `Proofs`. There are no custom axioms
asserting supporting complexity-theoretic results. In particular, Theorem 7.1
uses the user-approved corrections to the certificate definitions: certified
instances may be empty words, and every sampled certificate must certify an
instance of the requested length. The original empty-word exclusion is retained
separately in `LiteralCertificateCoverage` for its verified counterexample.
-/

namespace ComplexityOfGenerators

/-- **Theorem 3.1 (Generability is Recursive Enumerability), p. 0:10.**
“RE = GEN.” The equality is between classes of languages over a fixed finite
alphabet. Neither decidability nor a time/space bound is assumed. -/
theorem theorem_3_1_generability_is_recursive_enumerability
    (α : Type) [Fintype α] : RE α = GEN α := by
  apply Set.Subset.antisymm
  · exact re_subset_gen α
  · exact gen_subset_re α

/-- **Theorem 5.1 (Cryptographic Separation), p. 0:15.**
“If collision-resistant hash functions exist, then PG ⊊ NP. In fact, P ⊈ PG.”
The assumption is the paper's unkeyed, uniform-attack collision resistance.
We specialise the word alphabet to binary for these bitstring complexity classes. -/
theorem theorem_5_1_cryptographic_separation
    (h : CollisionResistantHashFunctionsExist) :
    PG Bool ⊂ NP Bool ∧ ¬ P Bool ⊆ PG Bool := by
  obtain ⟨hash, secure⟩ := h
  have collision_decidable := hash.binaryCollisionLanguage_mem_p
  have not_generable := hash.binaryCollisionLanguage_not_mem_pg secure
  refine ⟨⟨pg_subset_np, ?_⟩, ?_⟩
  · intro reverseContainment
    exact not_generable (reverseContainment (p_subset_np collision_decidable))
  · intro containment
    exact not_generable (containment collision_decidable)

/-- **Theorem 6.1, p. 0:22.** “PSPACEG = PSPACE.”
This theorem is unrelativised, exactly as stated. Oracle equality is Proposition
6.5, not another main theorem; no oracle or cryptographic assumption is added. -/
theorem theorem_6_1_polynomial_space_generation
    (α : Type) [Fintype α] : PSPACEG α = PSPACE α := by
  apply Set.Subset.antisymm
  · exact pspaceg_subset_pspace
  · exact pspace_subset_pspaceg

/-- **Theorem 7.1 (Generators are Certificate Schemes), p. 0:24.**
“(1) L is generable in polynomial time (L ∈ PG).
(2) There exists a polynomial-time verifier V for L, and V has a certificate scheme.”
The verifier is existentially quantified, rather than fixed in advance.
There is no extra assumption `L ∈ NP` or `[] ∉ L` in the paper or here.
The user-approved corrections allow empty instances and require every sampled
certificate to certify an instance of the requested length. -/
theorem theorem_7_1_generators_are_certificate_schemes
    {α : Type} [Fintype α] (L : Language α) :
    L ∈ PG α ↔ ∃ V : PolynomialVerifier L, HasCertificateScheme V := by
  constructor
  · exact pg_has_certificateScheme
  · rintro ⟨V, scheme⟩
    exact hasCertificateScheme_mem_pg scheme

/-- **Theorem 7.2 (Efficient Generators are not Composable), p. 0:25.**
“If NP ≠ coNP, then PG is not closed under complementation. If collision-resistant
hash functions exist, then PG is not closed under intersection.”
The two clauses have independent assumptions; neither is required for the other.
Closure is extensional language closure, as in the theorem's textual statement. -/
theorem theorem_7_2_efficient_generators_are_not_composable :
    (NP Bool ≠ coNP Bool → ¬ ClosedUnderComplement (PG Bool)) ∧
    (CollisionResistantHashFunctionsExist → ¬ ClosedUnderIntersection (PG Bool)) :=
  ⟨pg_not_complement_closed, pg_not_intersection_closed⟩

end ComplexityOfGenerators
