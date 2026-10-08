import ComplexityOfGenerators.Foundations.BoundedGeneration
import ComplexityOfGenerators.Foundations.Cryptography
import ComplexityOfGenerators.Foundations.Probability

/-!
# Probability and support in the collision-generator reduction

This is the mathematical part of Proposition 5.2 / Theorem 5.1. The simulation
hypothesis in `collision_generator_contradiction` is explicit: a constructor must
still turn the generator at size `2*(n+1)+1` into a collision finder at parameter
`n`. It is not supplied as an axiom, an instance, or an unfinished proof.
-/

namespace ComplexityOfGenerators

open MeasureTheory
open scoped ENNReal

/-- Exact output length determines the hash index. This also checks the corrected
`n+1`-bit preimage convention, rather than assuming Definition 5.5's ill-typed index. -/
theorem HashFunction.collision_member_parameter (h : HashFunction) (n : ℕ)
    (w : List PairSymbol) (member : w ∈ h.collisionLanguage)
    (length : w.length = 2 * (n + 1) + 1) :
    ∃ x y : BitString, h.IsCollision n x y ∧ w = encodePair x y := by
  obtain ⟨m, x, y, collision, rfl⟩ := member
  obtain ⟨a, b, rfl, rfl, different, equalHash⟩ := collision
  simp only [encodePair_length, bitsWord_length] at length
  have parameter : m = n := by omega
  subst m
  exact ⟨bitsWord a, bitsWord b, ⟨a, b, rfl, rfl, different, equalHash⟩, rfl⟩

/-- A finder that outputs a genuine collision on every full-budget seed has
success event equal to the whole stream space; no distribution-uniformity
assumption or individual-word probability lower bound is used. -/
theorem collisionSuccess_eq_univ_of_full_seeds (h : HashFunction) (A : CollisionFinder)
    (n t : ℕ) (success : ∀ bits : BitString, bits.length = t →
      ∃ x y : BitString, A.machine.Produces (generatorData n) bits (encodePair x y) ∧
        h.IsCollision n x y) : collisionSuccess h A n = Set.univ := by
  apply Set.eq_univ_of_forall
  intro stream
  obtain ⟨x, y, produces, collision⟩ := success (streamPrefix stream t)
    (streamPrefix_length stream t)
  exact ⟨x, y, streamPrefix stream t, stream_mem_prefix_cylinder stream t,
    produces, collision⟩

theorem HashFunction.no_perfect_collision_finder (h : HashFunction)
    (secure : h.CollisionResistant) (A : CollisionFinder)
    (perfect : ∀ n, fairCoinMeasure (collisionSuccess h A n) = 1) : False := by
  apply secure
  let q : PolynomialBound := ⟨2, 0, by decide⟩
  refine ⟨A, q, ?_⟩
  have all : {n : ℕ | (q n : ℝ≥0∞)⁻¹ < fairCoinMeasure (collisionSuccess h A n)} =
      Set.univ := by
    apply Set.eq_univ_of_forall
    intro n
    change (q n : ℝ≥0∞)⁻¹ < fairCoinMeasure (collisionSuccess h A n)
    rw [perfect n]
    norm_num [q, PolynomialBound.eval]
  rw [all]
  exact Set.infinite_univ

/-- A collision generator and a verified parameter-changing simulation would
break the paper's exact uniform collision-resistance assumption. The computational
implementation obligation is separated from the fully proved probability argument. -/
theorem collision_generator_contradiction (h : HashFunction) (secure : h.CollisionResistant)
    (G : GeneratorFamily PairSymbol)
    (language : G.toUniformGenerators.language = h.collisionLanguage)
    (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time)
    (A : CollisionFinder)
    (simulation : ∀ n bits w,
      G.machine.Produces (generatorData (2 * (n + 1) + 1)) bits w →
        A.machine.Produces (generatorData n) bits w) : False := by
  apply h.no_perfect_collision_finder secure A
  intro n
  let size := 2 * (n + 1) + 1
  have layer : G.toUniformGenerators.layer size = lengthSlice h.collisionLanguage size := by
    rw [G.layer_eq_lengthSlice, language]
  have nonempty : (G.toUniformGenerators.layer size).Nonempty := by
    rw [layer]
    exact h.collision_slice_nonempty n
  have full : ∀ bits : BitString, bits.length = seed size →
      ∃ x y, A.machine.Produces (generatorData n) bits (encodePair x y) ∧
        h.IsCollision n x y := by
    intro bits length
    obtain ⟨w, produces⟩ := ((bound size).2 bits length).2 nonempty
    have seed_nonempty : bits ≠ [] := by
      intro empty
      have positive := seed.positive size
      simp [empty] at length
      omega
    have member : w ∈ G.toUniformGenerators.layer size := ⟨bits, seed_nonempty, produces⟩
    rw [layer] at member
    obtain ⟨x, y, collision, rfl⟩ := h.collision_member_parameter n w member.1 member.2
    exact ⟨x, y, simulation n bits _ produces, collision⟩
  rw [collisionSuccess_eq_univ_of_full_seeds h A n (seed size) full]
  exact measure_univ

end ComplexityOfGenerators
