import ComplexityOfGenerators.Proofs.FallbackGeneration
import ComplexityOfGenerators.Proofs.NondeterministicUnion
import ComplexityOfGenerators.Proofs.PolynomialCollisionDecision
import ComplexityOfGenerators.Proofs.PolynomialGenerationContainment
import ComplexityOfGenerators.Proofs.EmptyWordGeneration
import ComplexityOfGenerators.ExpectedGenerators

/-!
# Intersection witnesses for expected-length generation

Add the empty word to the binary collision language, and then use the existing
native constant-bit fallback generators.  Both resulting languages have a
nonempty slice at every length, including zero.  Their exact-length polynomial
generators can therefore also be used as expected-length generators with mean
equal to the requested index.  Their intersection is the collision language
with only the empty word added.

This construction avoids a new prefix-removal compiler: any nonempty word in
the intersection is already a canonical binary collision encoding.
-/

namespace ComplexityOfGenerators

namespace HashFunction

/-- A bounded exceptional output supplies the size-zero slice without changing
the collision-finding content of any positive-length output. -/
def collisionWithEmpty (h : HashFunction) : Language Bool :=
  h.binaryCollisionLanguage ∪ {[]}

/-- The two fallback languages used for expected-length nonclosure. -/
def collisionFallback (h : HashFunction) (bit : Bool) : Language Bool :=
  h.collisionWithEmpty ∪ constantBitLanguage bit

theorem collisionWithEmpty_mem_np (h : HashFunction) :
    h.collisionWithEmpty ∈ NP Bool :=
  np_union (p_subset_np h.binaryCollisionLanguage_mem_p)
    (pg_subset_np (empty_word_language_in_pg Bool))

/-- This membership uses the already verified native fallback machine. -/
theorem collisionFallback_mem_pg (h : HashFunction) (bit : Bool) :
    h.collisionFallback bit ∈ PG Bool :=
  np_union_constantBit_mem_pg h.collisionWithEmpty_mem_np bit

theorem collisionFallback_slice_nonempty (h : HashFunction) (bit : Bool) (n : ℕ) :
    (lengthSlice (h.collisionFallback bit) n).Nonempty := by
  by_cases zero : n = 0
  · subst n
    exact ⟨[], Or.inl (Or.inr rfl), rfl⟩
  · refine ⟨List.replicate n bit, Or.inr ?_, by simp⟩
    exact ⟨by simpa using zero, fun letter member => (List.mem_replicate.mp member).2⟩

/-- The same native exact-length fallback machine has expected length exactly
equal to every index, expected polynomial runtime, and short output witnesses. -/
theorem collisionFallback_mem_elepg (h : HashFunction) (bit : Bool) :
    h.collisionFallback bit ∈ ELEPG Bool :=
  pg_mem_elepg_of_nonempty_slices (h.collisionFallback_mem_pg bit)
    (h.collisionFallback_slice_nonempty bit)

theorem collisionFallbacks_intersection (h : HashFunction) :
    h.collisionFallback false ∩ h.collisionFallback true = h.collisionWithEmpty :=
  fallback_intersection h.collisionWithEmpty

/-- Collision encodings at distinct security parameters have distinct lengths,
so the intersection witness is infinite even before adding the empty word. -/
theorem binaryCollisionLanguage_infinite (h : HashFunction) :
    h.binaryCollisionLanguage.Infinite := by
  classical
  let word : ℕ → BitString := fun n => (h.binary_collision_slice_nonempty n).choose
  have property (n : ℕ) :
      word n ∈ h.binaryCollisionLanguage ∧ (word n).length = 4 * (n + 1) + 2 :=
    (h.binary_collision_slice_nonempty n).choose_spec
  apply Set.infinite_of_injective_forall_mem (f := word)
  · intro n m equal
    have lengths := congrArg List.length equal
    rw [(property n).2, (property m).2] at lengths
    omega
  · exact fun n => (property n).1

theorem collisionWithEmpty_infinite (h : HashFunction) :
    h.collisionWithEmpty.Infinite :=
  h.binaryCollisionLanguage_infinite.mono (fun _ member => Or.inl member)

theorem collisionFallback_infinite (h : HashFunction) (bit : Bool) :
    (h.collisionFallback bit).Infinite :=
  h.collisionWithEmpty_infinite.mono (fun _ member => Or.inl member)

/-- The class-independent end of the nonclosure argument. -/
theorem not_intersection_closed_of_collisionWithEmpty (h : HashFunction)
    (C : LanguageClass Bool)
    (left : h.collisionFallback false ∈ C)
    (right : h.collisionFallback true ∈ C)
    (outside : h.collisionWithEmpty ∉ C) :
    ¬ ClosedUnderIntersection C := by
  intro closed
  apply outside
  rw [← h.collisionFallbacks_intersection]
  exact closed _ _ left right

/-- A stronger witness than mere failure of closure: the intersection remains
infinite, so the obstruction is not ELEPG's exclusion of finite languages. -/
theorem collisionFallbacks_infinite_intersection_witness (h : HashFunction)
    (C : LanguageClass Bool)
    (left : h.collisionFallback false ∈ C)
    (right : h.collisionFallback true ∈ C)
    (outside : h.collisionWithEmpty ∉ C) :
    ∃ A B : Language Bool,
      A ∈ C ∧ B ∈ C ∧ (A ∩ B).Infinite ∧ A ∩ B ∉ C := by
  refine ⟨h.collisionFallback false, h.collisionFallback true, left, right, ?_, ?_⟩
  · rw [h.collisionFallbacks_intersection]
    exact h.collisionWithEmpty_infinite
  · rwa [h.collisionFallbacks_intersection]

/-- Once the expected-time collision reduction excludes bounded exceptional
outputs, the already constructed native fallback generators refute closure. -/
theorem elepg_not_intersection_closed_of_collisionWithEmpty (h : HashFunction)
    (outside : h.collisionWithEmpty ∉ ELEPG Bool) :
    ¬ ClosedUnderIntersection (ELEPG Bool) :=
  h.not_intersection_closed_of_collisionWithEmpty (ELEPG Bool)
    (h.collisionFallback_mem_elepg false) (h.collisionFallback_mem_elepg true) outside

/-- The ELEPG nonclosure witnesses have an infinite intersection.  The premise
is explicitly the remaining cryptographic collision obstruction. -/
theorem elepg_infinite_intersection_witness_of_collisionWithEmpty (h : HashFunction)
    (outside : h.collisionWithEmpty ∉ ELEPG Bool) :
    ∃ A B : Language Bool,
      A ∈ ELEPG Bool ∧ B ∈ ELEPG Bool ∧ (A ∩ B).Infinite ∧ A ∩ B ∉ ELEPG Bool :=
  h.collisionFallbacks_infinite_intersection_witness (ELEPG Bool)
    (h.collisionFallback_mem_elepg false) (h.collisionFallback_mem_elepg true) outside

/-- Structural native-machine witnesses.  The cryptographic part of the ELEPG
argument is precisely exclusion of their infinite intersection. -/
theorem collisionFallbacks_witness (h : HashFunction) :
    h.collisionFallback false ∈ PG Bool ∧
    h.collisionFallback true ∈ PG Bool ∧
    (∀ n, (lengthSlice (h.collisionFallback false) n).Nonempty) ∧
    (∀ n, (lengthSlice (h.collisionFallback true) n).Nonempty) ∧
    h.collisionFallback false ∩ h.collisionFallback true = h.collisionWithEmpty ∧
    h.collisionWithEmpty.Infinite :=
  ⟨h.collisionFallback_mem_pg false, h.collisionFallback_mem_pg true,
    h.collisionFallback_slice_nonempty false, h.collisionFallback_slice_nonempty true,
    h.collisionFallbacks_intersection, h.collisionWithEmpty_infinite⟩

end HashFunction

end ComplexityOfGenerators
