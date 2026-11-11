import ComplexityOfGenerators.ExpectedGenerators
import ComplexityOfGenerators.Foundations.StreamSemanticsProperties
import ComplexityOfGenerators.Foundations.StreamPrefixExecution
import ComplexityOfGenerators.Proofs.ExpectedCollisionReduction
import ComplexityOfGenerators.Proofs.ExpectedCollisionFinder
import ComplexityOfGenerators.Proofs.ExpectedGeneratorNonclosure

/-!
# ELEPG collision non-generability and infinite-intersection nonclosure

The attacker is the actual finite-control bounded-search machine. The argument
only uses first moments of length and runtime; it does not require variance,
uniform output probabilities, or independence of length and runtime. The tail
obstruction even permits the empty word as an exceptional output and does not
use the polynomially short accepting-path clause of ELEPG.
-/

namespace ComplexityOfGenerators

open MeasureTheory Simulation
open scoped ENNReal

noncomputable section

theorem expectedCollisionFinder_stream_success (h : HashFunction)
    (G : UniformGenerators Bool) (clock : PolynomialBound)
    (sound : ∀ i word, word ∈ G.layer i → word = [] ∨ word ∈ h.binaryCollisionLanguage)
    (n i : ℕ) (index : i ≤ 2 * expectedCollisionLength n) :
    {stream | G.machine.streamLength (generatorData i) stream = expectedCollisionLength n ∧
      G.machine.streamRuntime (generatorData i) stream ≤ (clock n : ℝ≥0∞)} ⊆
        collisionSuccess h (ExpectedCollisionSearch.finder G.machine clock) n := by
  rintro stream ⟨length, runtime⟩
  obtain ⟨word, run, wordLength⟩ :=
    G.machine.streamLength_run_streamPrefix_of_runtime_le (generatorData i) runtime
  obtain ⟨x, y, produces, collision⟩ := ExpectedCollisionSearch.finder_success_of_run
    h G clock sound n i (streamPrefix stream (clock n + 1)) word
    (streamPrefix_length stream _) index run (wordLength.trans length)
  exact ⟨x, y, streamPrefix stream (clock n + 1),
    stream_mem_prefix_cylinder stream _, produces, collision⟩

/-- A stronger tail obstruction than ELEPG non-membership: means and expected
runtime bounds need hold only eventually; exceptional empty outputs are allowed. -/
theorem HashFunction.expected_collision_tail_impossible (h : HashFunction)
    (secure : h.CollisionResistant) (G : UniformGenerators Bool) (firstIndex : ℕ)
    (p : PolynomialBound)
    (sound : ∀ i word, word ∈ G.layer i → word = [] ∨ word ∈ h.binaryCollisionLanguage)
    (mean : ∀ i, firstIndex ≤ i →
      G.machine.expectedLength (generatorData i) = (i : ℝ≥0∞))
    (runtime : ∀ i, firstIndex ≤ i →
      G.machine.expectedRuntime (generatorData i) ≤ (p i : ℝ≥0∞)) : False := by
  apply h.expected_collision_generator_contradiction secure G firstIndex p
    (fun i _ word member => (sound i word member).symm) mean runtime
    (ExpectedCollisionSearch.finder G.machine (expectedCollisionClock p))
  exact fun n i index => expectedCollisionFinder_stream_success h G
    (expectedCollisionClock p) sound n i index

/-- The bounded-exception form needed for nonclosure: adding the empty word
does not restore expected-length expected-polynomial-time generability. -/
theorem HashFunction.not_mem_elepg_of_subset_collisionWithEmpty (h : HashFunction)
    (secure : h.CollisionResistant) {L : Language Bool}
    (subset : L ⊆ h.collisionWithEmpty) : L ∉ ELEPG Bool := by
  rintro ⟨_, G, language, mean, p, runtime, _⟩
  have sound (i : ℕ) (word : BitString) (member : word ∈ G.layer i) :
      word = [] ∨ word ∈ h.binaryCollisionLanguage := by
    have inLanguage : word ∈ L := language ▸ (show word ∈ G.language from ⟨i, member⟩)
    rcases subset inLanguage with collision | empty
    · exact Or.inr collision
    · exact Or.inl empty
  apply h.expected_collision_tail_impossible secure G 1 p sound
    (fun i _ => mean i)
  intro i positive
  apply runtime i
  apply G.machine.generatedLanguage_nonempty_of_expectedLength_pos
  rw [mean i]
  exact_mod_cast (show 0 < i by omega)

theorem HashFunction.binaryCollisionLanguage_not_mem_elepg (h : HashFunction)
    (secure : h.CollisionResistant) : h.binaryCollisionLanguage ∉ ELEPG Bool :=
  h.not_mem_elepg_of_subset_collisionWithEmpty secure (fun _ member => Or.inl member)

theorem HashFunction.collisionWithEmpty_not_mem_elepg (h : HashFunction)
    (secure : h.CollisionResistant) : h.collisionWithEmpty ∉ ELEPG Bool :=
  h.not_mem_elepg_of_subset_collisionWithEmpty secure (fun _ member => member)

theorem elepg_not_intersection_closed (hashes : CollisionResistantHashFunctionsExist) :
    ¬ ClosedUnderIntersection (ELEPG Bool) := by
  obtain ⟨h, secure⟩ := hashes
  exact h.elepg_not_intersection_closed_of_collisionWithEmpty
    (h.collisionWithEmpty_not_mem_elepg secure)

/-- Cryptographic nonclosure persists when the intersection is infinite, so it
cannot be explained merely by the definition's exclusion of finite languages. -/
theorem elepg_infinite_intersection_witness (hashes : CollisionResistantHashFunctionsExist) :
    ∃ A B : Language Bool, A ∈ ELEPG Bool ∧ B ∈ ELEPG Bool ∧
      (A ∩ B).Infinite ∧ A ∩ B ∉ ELEPG Bool := by
  obtain ⟨h, secure⟩ := hashes
  exact h.elepg_infinite_intersection_witness_of_collisionWithEmpty
    (h.collisionWithEmpty_not_mem_elepg secure)

end

end ComplexityOfGenerators
