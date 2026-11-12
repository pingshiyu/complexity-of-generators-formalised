import ComplexityOfGenerators.Cryptography
import ComplexityOfGenerators.Proofs.GenerabilityContainment
import ComplexityOfGenerators.Proofs.RecognizabilityContainment
import ComplexityOfGenerators.Proofs.PolynomialGenerationContainment
import ComplexityOfGenerators.Proofs.PolynomialCollisionDecision
import ComplexityOfGenerators.Foundations.LanguageClosure
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
import ComplexityOfGenerators.Examples.SATNative.ExactRecursive
import ComplexityOfGenerators.Examples.HAMPATHNative.ExactRecursive

import ComplexityOfGenerators.Proofs.PaperCertificateEquivalence
import ComplexityOfGenerators.Proofs.PaperExactRecursiveGeneration
import ComplexityOfGenerators.Proofs.PaperExactRecursiveLegacy
import ComplexityOfGenerators.Proofs.PairCollisionDecision
import ComplexityOfGenerators.Proofs.PairCollisionNonGenerability
import ComplexityOfGenerators.Proofs.AlphabetIntersectionNonclosure
import ComplexityOfGenerators.Proofs.AlphabetComplementNonclosure

/-!
# Current PLDI27 theorem API

This file collects the proved results of the current paper, using its current
numbering, together with their resource specialisations and concrete examples.
Historical theorem aliases and retained certificate conventions are collected
separately in `HistoricalTheorems`. The root package imports both APIs.

Every declaration has a kernel-checked proof in the model identified by its
type. General resource results use the explicit multitape model. The current
certificate and exact-recursive interfaces use the paper's accepting-run bounds;
collision statements use the literal separated-pair language. Model conventions
are recorded in `DEFINITION_CROSS_REFERENCE.md` and `ARTIFACT_README.md`.
-/

namespace ComplexityOfGenerators

/-! ## Unconstrained generation -/

/-- **Current Theorem 3.1 (Generability is Recursive Enumerability).**
“RE = GEN.” The equality is between classes of languages over a fixed finite
alphabet. Neither decidability nor a time/space bound is assumed. -/
theorem theorem_3_1_generability_is_recursive_enumerability
    (α : Type) [Fintype α] : RE α = GEN α := by
  apply Set.Subset.antisymm
  · exact re_subset_gen α
  · exact gen_subset_re α

/-- A language outside RE cannot be generated (Section 3). -/
theorem corollary_non_recursively_enumerable_not_generable
    {α : Type} [Fintype α] {L : Language α} (outside : L ∉ RE α) : L ∉ GEN α :=
  fun generated => outside (gen_subset_re α generated)

/-! ## Resource bounds -/

/-- Current Lemma 4.1 in the native evaluator's convention: a complete
prefix has `time + 1` bits because terminal observation takes no transition. -/
theorem lemma_4_1_acceptance_at_time_bound {I A O : Type}
    (M : Machine I A O) (data : InputData I A) (time : ℕ)
    (generator : M.IsGenerator data) (bound : M.AcceptingTimeBound data time)
    (bits : BitString) (length : bits.length = time + 1) :
    M.Accepts data bits ↔ (M.generatedLanguage data).Nonempty :=
  M.accepts_full_prefix_of_acceptingTimeBound data time generator bound bits length

/-- The general TIME half of Proposition 4.1 uses actual finite multitape
machines, with every constructor and source transition charged. -/
theorem proposition_4_1_time {α : Type} [Fintype α] (time : ℕ → ℕ)
    (constructible : Multitape.TimeConstructible time) (dominates : ∀ n, n < time n) :
    Multitape.GTIME α time ⊆ Multitape.NTIME α time :=
  Multitape.gtime_subset_ntime time constructible (fun n => (dominates n).le)

/-- The general SPACE half of Proposition 4.1, including charged binary
index handling and an actual space-constructed finite-configuration clock. -/
theorem proposition_4_1_space {α : Type} [Fintype α] (space : ℕ→ℕ)
    (constructible : Multitape.SpaceConstructible space) (dominates : ∀ n,Nat.log 2 n<space n) :
    Multitape.GSPACE α space ⊆ Multitape.NSPACE α space :=
  Multitape.gspace_subset_nspace space constructible dominates

/-- Polynomial resource specialisations of Proposition 4.1. -/
theorem proposition_4_1_polynomial (α : Type) [Fintype α] :
    PG α ⊆ NP α ∧ PSPACEG α ⊆ PSPACE α := ⟨pg_subset_np, pspaceg_subset_pspace⟩

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

/-- The generator-to-decider TIME direction of Proposition 4.2. -/
theorem proposition_4_2_time_forward {α : Type} [Fintype α] (time : ℕ → ℕ)
    (constructible : Multitape.TimeConstructible time) (dominates : ∀ n, n ≤ time n) :
    Multitape.GTIMEUpTo α time ⊆ Multitape.NTIME α time :=
  Multitape.gtimeUpTo_subset_ntime time constructible dominates

/-- Polynomial-time specialisation of Proposition 4.2 over every finite
alphabet, including the empty alphabet. No arbitrary-resource equality is
asserted by this declaration. -/
theorem proposition_4_2_polynomial_up_to (α : Type) [Fintype α] : PGUpTo α = NP α :=
  pgUpTo_eq_np

/-- Polynomial-space specialisation of Proposition 4.2 over any finite alphabet. -/
theorem proposition_4_2_polynomial_space_up_to (α : Type) [Fintype α] :
    PSPACEGUpTo α = PSPACE α := pspacegUpTo_eq_pspace

/-- Polynomial binary-alphabet specialisation of Proposition 4.2. The
general multitape equality is exposed separately above. -/
theorem proposition_4_2_polynomial_binary_up_to : PGUpTo Bool = NP Bool :=
  pgUpTo_eq_np_bool

/-! ## Polynomial and expected-time generation -/

/-- Current Corollary 5.1: polynomial-time exact generation is in NP. -/
theorem corollary_5_1_polynomial_generation_subset_np
    (α : Type) [Fintype α] : PG α ⊆ NP α := pg_subset_np

/-- Current Proposition 5.1 for the concrete padded-CNF encoding. -/
theorem proposition_5_1_cnf_sat_polynomial_generation :
    Examples.PaddedCNF.language ∈ PG Examples.PaddedCNF.Symbol :=
  Examples.PaddedCNF.language_mem_pg

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

/-- The collision-language observation in Section 5.3 needs no security
assumption; the native hash implementations give a polynomial decider. -/
theorem observation_collision_language_polynomial_decision (h : HashFunction) :
    h.collisionLanguage ∈ P PairSymbol := h.collisionLanguage_mem_p

/-- Current Theorem 5.2 for the literal `x#y` language over `PairSymbol`. The stronger raw result
below removes the global fast-path condition as well. -/
theorem theorem_5_2_collision_non_generability
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.collisionLanguage ∉ ELEPG PairSymbol :=
  h.collisionLanguage_not_mem_elepg secure

/-- **Current Theorem 5.2, stronger raw form.** Neither short accepting paths
nor polynomial producing-index coverage is assumed. Only infinitely many active
indices and the two first-moment bounds are needed. -/
theorem theorem_5_2_raw_expected_length_collision_non_generability
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.collisionLanguage ∉ ExpectedLengthExpectedPolynomialTime PairSymbol :=
  h.collisionLanguage_not_mem_expectedLengthExpectedPolynomialTime secure

/-- The PG and EPG exclusions follow from the stronger collision obstruction. -/
theorem corollary_5_2_collision_non_generability
    (h : HashFunction) (secure : h.CollisionResistant) :
    h.collisionLanguage ∉ PG PairSymbol ∧ h.collisionLanguage ∉ EPG PairSymbol :=
  ⟨h.collisionLanguage_not_mem_pg secure,h.collisionLanguage_not_mem_epg secure⟩

/-- The class separation illustrated in the current paper: a collision
language in P witnesses both strict PG containment in NP and `P ⊈ PG`. -/
theorem corollary_collision_resistance_separates_polynomial_generation
    (hashes : CollisionResistantHashFunctionsExist) :
    PG Bool ⊂ NP Bool ∧ ¬ P Bool ⊆ PG Bool := by
  obtain ⟨hash, secure⟩ := hashes
  have decidable := hash.binaryCollisionLanguage_mem_p
  have outside := hash.binaryCollisionLanguage_not_mem_pg secure
  refine ⟨⟨pg_subset_np, ?_⟩, ?_⟩
  · intro reverseContainment
    exact outside (reverseContainment (p_subset_np decidable))
  · intro containment
    exact outside (containment decidable)

/-! ## Conditions for polynomial generation -/

/-- Current Proposition 6.1, with certificates in the instance alphabet,
including the empty certificate, and accepting-run bounds for both generators. -/
theorem proposition_6_1_generators_are_certificate_schemes
    {α : Type} [Fintype α] (L : Language α) :
    L ∈ PG α ↔ ∃ V : PaperCertificates.PolynomialVerifier L,
      PaperCertificates.HasCertificateScheme V :=
  PaperCertificates.certificate_equivalence L

/-- Current Proposition 6.2. The inverse generator is constrained only on the
paper's bounded labels, with accepting-run bounds rather than trial budgets. -/
theorem proposition_6_2_exact_recursive_generation
    {α : Type} [Fintype α] {L : Language α}
    (generable : PaperExactlyRecursivelyGenerable L) : L ∈ PG α :=
  paperExactlyRecursivelyGenerable_mem_pg generable

/-- The SAT example has actual native polynomial self-reduction machines. -/
theorem example_sat_polynomial_self_reduction :
    Nonempty (PolynomialSelfReduction Examples.PaddedCNF.selfReduction) :=
  ⟨Examples.PaddedCNF.polynomialSelfReduction⟩

/-- The current SAT exact-recursive example, with the padded-CNF codec. -/
theorem example_sat_exact_recursive_generation :
    PaperExactlyRecursivelyGenerable Examples.PaddedCNF.language :=
  paperExactlyRecursivelyGenerable_of_legacy Examples.PaddedCNF.exactlyRecursivelyGenerable

/-- The HAMPATH example has actual native polynomial self-reduction machines. -/
theorem example_hampath_polynomial_self_reduction :
    Nonempty (PolynomialSelfReduction Examples.HAMPATH.selfReduction) :=
  ⟨Examples.HAMPATH.polynomialSelfReduction⟩

/-- The current HAMPATH exact-recursive example uses loop-free directed
adjacency matrices; longer cycles are allowed. -/
theorem example_hampath_exact_recursive_generation :
    PaperExactlyRecursivelyGenerable Examples.HAMPATH.language :=
  paperExactlyRecursivelyGenerable_of_legacy Examples.HAMPATH.exactlyRecursivelyGenerable

/-- The concrete HAMPATH construction yields polynomial exact generation. -/
theorem example_hampath_polynomial_generation :
    Examples.HAMPATH.language ∈ PG Examples.HAMPATH.Symbol :=
  Examples.HAMPATH.language_mem_pg

/-! ## Compositionality -/

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

/-- **Current Theorem 6.1, complement clause.** The alphabet has at least two
symbols, following the paper's alphabet convention. The classes use the current
expected-time and active-index definitions. -/
theorem theorem_6_1_complement_nonclosure {α : Type} [Fintype α] [Nontrivial α]
    (different : NP α ≠ coNP α) :
    ¬ ClosedUnderComplement (PG α) ∧
    ¬ ClosedUnderComplement (EPG α) ∧ ¬ ClosedUnderComplement (ELEPG α) :=
  ⟨pg_not_complement_closed_alphabet different,epg_not_complement_closed_alphabet different,
    elepg_not_complement_closed_alphabet different⟩

/-- **Current Theorem 6.1, intersection clause.** Every class has witnesses
whose intersection is infinite, avoiding a finite-language boundary artefact. -/
theorem theorem_6_1_infinite_intersection_nonclosure {α : Type} [Fintype α] [Nontrivial α]
    (hashes : CollisionResistantHashFunctionsExist) :
    (∃ A B : Language α, A ∈ PG α ∧ B ∈ PG α ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ PG α) ∧
    (∃ A B : Language α, A ∈ EPG α ∧ B ∈ EPG α ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ EPG α) ∧
    (∃ A B : Language α, A ∈ ELEPG α ∧ B ∈ ELEPG α ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ ELEPG α) :=
  ⟨pg_infinite_intersection_witness_alphabet hashes,
    epg_infinite_intersection_witness_alphabet hashes,
    elepg_infinite_intersection_witness_alphabet hashes⟩

end ComplexityOfGenerators
