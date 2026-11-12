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
import ComplexityOfGenerators.Proofs.ExactRecursiveGeneration
import ComplexityOfGenerators.Proofs.ELEPGCollision
import ComplexityOfGenerators.Proofs.ExpectedGenerationContainment
import ComplexityOfGenerators.Proofs.ExpectedLengthContainment
import ComplexityOfGenerators.Proofs.ExpectedNonclosure
import ComplexityOfGenerators.Proofs.UpToGeneration
import ComplexityOfGenerators.Proofs.AcceptingTimeGeneration
import ComplexityOfGenerators.Proofs.UpToPolynomialGeneration
import ComplexityOfGenerators.Proofs.UpToSpaceGeneration
import ComplexityOfGenerators.Proofs.PolynomialUnion
import ComplexityOfGenerators.Proofs.PolynomialConcatenation
import ComplexityOfGenerators.Proofs.PolynomialStar
import ComplexityOfGenerators.Proofs.ExpectedUnion
import ComplexityOfGenerators.Proofs.ExpectedConcatenation
import ComplexityOfGenerators.Proofs.ExpectedStar
import ComplexityOfGenerators.Proofs.ELEPGStar
import ComplexityOfGenerators.Proofs.ELEPGBinary
import ComplexityOfGenerators.Proofs.Multitape.TimeContainment
import ComplexityOfGenerators.Proofs.Multitape.TimeConverse
import ComplexityOfGenerators.Proofs.Multitape.SpaceContainment

/-!
# Public theorem API

The current PLDI27 numbering is used by the new declarations below. Historical
entry points for the older bundled manuscript are retained explicitly as such;
their numbers must not be read as claims about the current paper's coverage.
See `CURRENT_PAPER_STATUS.md` for completed results and remaining obligations.
Every declaration has a kernel-checked proof in the finite machine model
identified by its type. General resource results use the explicit multitape model.
-/

namespace ComplexityOfGenerators

/-- The general TIME half of Proposition 4.1 uses actual finite multitape
machines, with every constructor and source transition charged. -/
theorem proposition_4_1_time {α : Type} [Fintype α] (time : ℕ → ℕ)
    (constructible : Multitape.TimeConstructible time) (dominates : ∀ n, n < time n) :
    Multitape.GTIME α time ⊆ Multitape.NTIME α time :=
  Multitape.gtime_subset_ntime time constructible (fun n => (dominates n).le)

/-- The generator-to-decider TIME direction of Proposition 4.2. -/
theorem proposition_4_2_time_forward {α : Type} [Fintype α] (time : ℕ → ℕ)
    (constructible : Multitape.TimeConstructible time) (dominates : ∀ n, n ≤ time n) :
    Multitape.GTIMEUpTo α time ⊆ Multitape.NTIME α time :=
  Multitape.gtimeUpTo_subset_ntime time constructible dominates

/-- The general SPACE half of Proposition 4.1, including charged binary
index handling and an actual space-constructed finite-configuration clock. -/
theorem proposition_4_1_space {α : Type} [Fintype α] (space : ℕ→ℕ)
    (constructible : Multitape.SpaceConstructible space) (dominates : ∀ n,Nat.log 2 n<space n) :
    Multitape.GSPACE α space ⊆ Multitape.NSPACE α space :=
  Multitape.gspace_subset_nspace space constructible dominates

/-- The complete TIME equality of Proposition 4.2. -/
theorem proposition_4_2_time {α : Type} [Fintype α] (time : ℕ→ℕ)
    (constructible : Multitape.TimeConstructible time) (monotone : Monotone time) (dominates : ∀ n,n≤time n) :
    Multitape.GTIMEUpTo α time = Multitape.NTIME α time :=
  Multitape.gtimeUpTo_eq_ntime time constructible monotone dominates

/-- The complete SPACE equality of Proposition 4.2, counting work cells on
all tapes of the actual fixed finite-bank machines. -/
theorem proposition_4_2_space {α : Type} [Fintype α] (space : ℕ→ℕ)
    (constructible : Multitape.SpaceConstructible space) (monotone : Monotone space) (dominates : ∀ n,n≤space n) :
    Multitape.GSPACEUpTo α space = Multitape.NSPACE α space :=
  Multitape.gspaceUpTo_eq_nspace space constructible monotone dominates

/-- Polynomial-time specialisation of Proposition 4.2 over every finite
alphabet, including the empty alphabet. No arbitrary-resource equality is
asserted by this declaration. -/
theorem proposition_4_2_polynomial_up_to (α : Type) [Fintype α] : PGUpTo α = NP α :=
  pgUpTo_eq_np

/-- Polynomial-space specialisation of Proposition 4.2 over any finite alphabet. -/
theorem proposition_4_2_polynomial_space_up_to (α : Type) [Fintype α] :
    PSPACEGUpTo α = PSPACE α := pspacegUpTo_eq_pspace

/-- Polynomial resource specialisations of Proposition 4.1. -/
theorem proposition_4_1_polynomial (α : Type) [Fintype α] :
    PG α ⊆ NP α ∧ PSPACEG α ⊆ PSPACE α := ⟨pg_subset_np, pspaceg_subset_pspace⟩

/-- Polynomial binary-alphabet specialisation of Proposition 4.2. The
general multitape equality is exposed separately above. -/
theorem proposition_4_2_polynomial_binary_up_to : PGUpTo Bool = NP Bool :=
  pgUpTo_eq_np_bool

/-- The native PG union clause of Proposition 6.3. -/
theorem proposition_6_3_pg_union {α : Type} [Fintype α] {L K : Language α}
    (left : L ∈ PG α) (right : K ∈ PG α) : L ∪ K ∈ PG α := pg_union left right

/-- The EPG union clause uses the actual bounded-phase/retry machines. -/
theorem proposition_6_3_epg_union {α : Type} [Fintype α] {L K : Language α}
    (left : L ∈ EPG α) (right : K ∈ EPG α) : L ∪ K ∈ EPG α := epg_union left right

/-- The current ELEPG union construction uses original-source calls. -/
theorem proposition_6_3_elepg_union {α : Type} [Fintype α] {L K : Language α}
    (left : L ∈ ELEPG α) (right : K ∈ ELEPG α) : L ∪ K ∈ ELEPG α := elepg_union left right

/-- The native PG concatenation clause of Proposition 6.3, with positive
support for every feasible factorisation and both empty-word endpoints. -/
theorem proposition_6_3_pg_concatenation {α : Type} [Fintype α] {L K : Language α}
    (left : L ∈ PG α) (right : K ∈ PG α) : IndexedSupport.concat L K ∈ PG α :=
  pg_concatenation left right

/-- Native expected-time concatenation preserves every supported split. -/
theorem proposition_6_3_epg_concatenation {α : Type} [Fintype α] {L K : Language α}
    (left : L ∈ EPG α) (right : K ∈ EPG α) : IndexedSupport.concat L K ∈ EPG α :=
  epg_concatenation left right

/-- The current ELEPG concatenation construction preserves raw first moments. -/
theorem proposition_6_3_elepg_concatenation {α : Type} [Fintype α] {L K : Language α}
    (left : L ∈ ELEPG α) (right : K ∈ ELEPG α) : IndexedSupport.concat L K ∈ ELEPG α :=
  elepg_concatenation left right

/-- The native PG Kleene-star clause of Proposition 6.3, including ε. -/
theorem proposition_6_3_pg_star {α : Type} [Fintype α] {L : Language α}
    (member : L ∈ PG α) : IndexedSupport.star L ∈ PG α := pg_star member

/-- The EPG star construction uses native certification and sequential retry,
with a polynomial expected runtime and a short path for every output. -/
theorem proposition_6_3_epg_star {α : Type} [Fintype α] {L : Language α}
    (member : L ∈ EPG α) : IndexedSupport.star L ∈ EPG α := epg_star member

/-- The current ELEPG star clause uses direct original-source calls and
polynomial word-length fast paths, with no per-layer fast-path premise. -/
theorem proposition_6_3_elepg_star {α : Type} [Fintype α] {L : Language α}
    (member : L ∈ ELEPG α) : IndexedSupport.star L ∈ ELEPG α := elepg_star member

/-- **Current Proposition 5.2.** Exact expected polynomial-time generation lies
between polynomial-time generation and nondeterministic polynomial time. -/
theorem proposition_5_2_expected_polynomial_generation
    (α : Type) [Fintype α] : PG α ⊆ EPG α ∧ EPG α ⊆ NP α :=
  pg_subset_epg_subset_np

/-- **Current Theorem 5.1.** The first inclusion is restricted to infinite
languages; the second derives a polynomial producing index from the
wordwise fast path using unary-index locality. -/
theorem theorem_5_1_expected_generation_containments
    (α : Type) [Fintype α] :
    (∀ L : Language α, L.Infinite → L ∈ EPG α → L ∈ ELEPG α) ∧
      ELEPG α ⊆ NP α :=
  ⟨fun _ infinite expected => epg_mem_elepg_of_infinite expected infinite,
    elepg_subset_np⟩

/-- **Current Theorem 5.2, stronger raw form.** Neither short accepting paths
nor polynomial producing-index coverage is assumed. Only infinitely many active
indices and the two first-moment bounds are needed. -/
theorem theorem_5_2_raw_expected_length_collision_non_generability
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.binaryCollisionLanguage ∉ ExpectedLengthExpectedPolynomialTime Bool :=
  h.binaryCollisionLanguage_not_mem_expectedLengthExpectedPolynomialTime secure

/-- The PG and EPG exclusions follow from the stronger collision obstruction. -/
theorem corollary_5_2_collision_non_generability
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.binaryCollisionLanguage ∉ PG Bool ∧ h.binaryCollisionLanguage ∉ EPG Bool := by
  have expected : h.binaryCollisionLanguage ∉ EPG Bool := by
    intro member
    exact h.binaryCollisionLanguage_not_mem_elepg secure
      (epg_mem_elepg_of_infinite member h.binaryCollisionLanguage_infinite)
  exact ⟨fun member => expected (pg_subset_epg member), expected⟩

/-- **Current Theorem 6.1, complement clause.** The three classes use the current
expected-time and active-index definitions. -/
theorem theorem_6_1_complement_nonclosure (different : NP Bool ≠ coNP Bool) :
    ¬ ClosedUnderComplement (PG Bool) ∧
    ¬ ClosedUnderComplement (EPG Bool) ∧ ¬ ClosedUnderComplement (ELEPG Bool) :=
  ⟨pg_not_complement_closed different, epg_not_complement_closed different,
    elepg_not_complement_closed different⟩

/-- **Current Theorem 6.1, intersection clause.** Every class has witnesses
whose intersection is infinite, avoiding a finite-language boundary artefact. -/
theorem theorem_6_1_infinite_intersection_nonclosure
    (hashes : CollisionResistantHashFunctionsExist) :
    (∃ A B : Language Bool, A ∈ PG Bool ∧ B ∈ PG Bool ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ PG Bool) ∧
    (∃ A B : Language Bool, A ∈ EPG Bool ∧ B ∈ EPG Bool ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ EPG Bool) ∧
    (∃ A B : Language Bool, A ∈ ELEPG Bool ∧ B ∈ ELEPG Bool ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ ELEPG Bool) :=
  ⟨pg_infinite_intersection_witness hashes, epg_infinite_intersection_witness hashes,
    elepg_infinite_intersection_witness hashes⟩

/-- **Theorem 3.1 (Generability is Recursive Enumerability), p. 0:10.**
“RE = GEN.” The equality is between classes of languages over a fixed finite
alphabet. Neither decidability nor a time/space bound is assumed. -/
theorem theorem_3_1_generability_is_recursive_enumerability
    (α : Type) [Fintype α] : RE α = GEN α := by
  apply Set.Subset.antisymm
  · exact re_subset_gen α
  · exact gen_subset_re α

/-- **Historical Theorem 5.1 (Cryptographic Separation).**
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

/-- **Historical Theorem 6.1.** “PSPACEG = PSPACE.”
This theorem is unrelativised, exactly as stated. Oracle equality is Proposition
6.5, not another main theorem; no oracle or cryptographic assumption is added. -/
theorem theorem_6_1_polynomial_space_generation
    (α : Type) [Fintype α] : PSPACEG α = PSPACE α := by
  apply Set.Subset.antisymm
  · exact pspaceg_subset_pspace
  · exact pspace_subset_pspaceg

/-- **Historical Theorem 7.1 (current Proposition 6.1).**
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
  exactlyRecursivelyGenerable_mem_pg h

/-- Expected-length extension of collision non-generability, using the same
native machine model and unkeyed uniform collision-resistance assumption.
No variance or concentration hypothesis is imposed. -/
theorem theorem_expected_length_collision_non_generability
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.binaryCollisionLanguage ∉ ELEPG Bool :=
  h.binaryCollisionLanguage_not_mem_elepg secure

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
