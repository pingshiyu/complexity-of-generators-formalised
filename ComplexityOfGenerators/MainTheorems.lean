import ComplexityOfGenerators.Cryptography
import ComplexityOfGenerators.Certificates

/-!
# Every result marked “Theorem” in the supplied paper

Source: `complexity-of-generators-formalisation.pdf`, *Complexity Theory of
Randomised Testing*. There are five numbered theorems. Each docstring below
quotes its mathematical statement and identifies its printed page number.

This is the **statement formalisation** stage: the five `sorry` bodies are
explicit proof obligations, not completed proofs. There are no custom axioms
asserting supporting complexity-theoretic results. In particular, Theorem 7.1
retains the literal certificate definitions and their documented boundary issue.
-/

namespace ComplexityOfGenerators

/-- **Theorem 3.1 (Generability is Recursive Enumerability), p. 0:10.**
“RE = GEN.” The equality is between classes of languages over a fixed finite
alphabet. Neither decidability nor a time/space bound is assumed. -/
theorem theorem_3_1_generability_is_recursive_enumerability
    (α : Type) [Fintype α] : RE α = GEN α := by
  sorry

/-- **Theorem 5.1 (Cryptographic Separation), p. 0:15.**
“If collision-resistant hash functions exist, then PG ⊊ NP. In fact, P ⊈ PG.”
The assumption is the paper's unkeyed, uniform-attack collision resistance.
We specialise the word alphabet to binary for these bitstring complexity classes. -/
theorem theorem_5_1_cryptographic_separation
    (h : CollisionResistantHashFunctionsExist) :
    PG Bool ⊂ NP Bool ∧ ¬ P Bool ⊆ PG Bool := by
  sorry

/-- **Theorem 6.1, p. 0:22.** “PSPACEG = PSPACE.”
This theorem is unrelativised, exactly as stated. Oracle equality is Proposition
6.5, not another main theorem; no oracle or cryptographic assumption is added. -/
theorem theorem_6_1_polynomial_space_generation
    (α : Type) [Fintype α] : PSPACEG α = PSPACE α := by
  sorry

/-- **Theorem 7.1 (Generators are Certificate Schemes), p. 0:24.**
“(1) L is generable in polynomial time (L ∈ PG).
(2) There exists a polynomial-time verifier V for L, and V has a certificate scheme.”
The verifier is existentially quantified, rather than fixed in advance.
There is no extra assumption `L ∈ NP` or `[] ∉ L` in the paper or here. -/
theorem theorem_7_1_generators_are_certificate_schemes
    {α : Type} [Fintype α] (L : Language α) :
    L ∈ PG α ↔ ∃ V : PolynomialVerifier L, HasCertificateScheme V := by
  sorry

/-- Closed under complement relative to the full universe of words. -/
def ClosedUnderComplement {α : Type} (C : LanguageClass α) : Prop :=
  ∀ L, L ∈ C → Lᶜ ∈ C

/-- Closed under binary language intersection. -/
def ClosedUnderIntersection {α : Type} (C : LanguageClass α) : Prop :=
  ∀ L K, L ∈ C → K ∈ C → L ∩ K ∈ C

/-- **Theorem 7.2 (Efficient Generators are not Composable), p. 0:25.**
“If NP ≠ coNP, then PG is not closed under complementation. If collision-resistant
hash functions exist, then PG is not closed under intersection.”
The two clauses have independent assumptions; neither is required for the other.
Closure is extensional language closure, as in the theorem's textual statement. -/
theorem theorem_7_2_efficient_generators_are_not_composable :
    (NP Bool ≠ coNP Bool → ¬ ClosedUnderComplement (PG Bool)) ∧
    (CollisionResistantHashFunctionsExist → ¬ ClosedUnderIntersection (PG Bool)) := by
  sorry

end ComplexityOfGenerators
