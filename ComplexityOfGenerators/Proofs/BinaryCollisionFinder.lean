import ComplexityOfGenerators.Proofs.BinaryCollisionReduction
import ComplexityOfGenerators.Simulation.VirtualIndexPolynomial

/-!
# The native collision-finder construction

The generator-to-finder reduction is now a concrete finite-control machine with
a proved polynomial time bound. It expands the physical family index, simulates
the generator, and decodes its binary output. No simulation hypothesis is added
to the collision-resistance assumption or to the non-generability theorem.
-/

namespace ComplexityOfGenerators

open Simulation MeasureTheory

noncomputable section

def binaryCollisionFinder (h : HashFunction) (G : GeneratorFamily Bool)
    (language : G.toUniformGenerators.language = h.binaryCollisionLanguage)
    (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time) : CollisionFinder where
  machine := collisionIndexMachine (binaryOutputDecoder G.machine)
  time := collisionIndexTime time
  bounded := collisionIndexMachine_timeBound (binaryOutputDecoder G.machine) time
    (binary_collision_decoder_timeBound h G language seed time bound)

/-- A polynomial generator for the binary collision language yields an actual
native collision finder which succeeds on every full-budget random tape. -/
theorem binaryCollisionFinder_full_trial (h : HashFunction) (G : GeneratorFamily Bool)
    (language : G.toUniformGenerators.language = h.binaryCollisionLanguage)
    (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time)
    (n : ℕ) (bits : BitString) (length : bits.length = seed (4 * (n + 1) + 2)) :
    ∃ x y : BitString, h.IsCollision n x y ∧
      (binaryCollisionFinder h G language seed time bound).machine.Produces (generatorData n) bits (encodePair x y) := by
  obtain ⟨x, y, collision, produced⟩ := binary_collision_decoder_full_trial h G language seed time bound n bits length
  exact ⟨x, y, collision, collisionIndexMachine_produces (binaryOutputDecoder G.machine) n bits _ produced⟩

/-- The cryptographic non-generability conclusion used in Theorem 5.1, with no
extra computational assumptions: the attacker and its runtime are constructed. -/
theorem HashFunction.binaryCollisionLanguage_not_mem_pg (h : HashFunction) (secure : h.CollisionResistant) :
    h.binaryCollisionLanguage ∉ PG Bool := by
  rintro ⟨G, language, seed, time, bound⟩
  let finder := binaryCollisionFinder h G language seed time bound
  apply h.no_perfect_collision_finder secure finder
  intro n
  have full : ∀ bits : BitString, bits.length = seed (4 * (n + 1) + 2) →
      ∃ x y, finder.machine.Produces (generatorData n) bits (encodePair x y) ∧ h.IsCollision n x y := by
    intro bits length
    obtain ⟨x, y, collision, produced⟩ := binaryCollisionFinder_full_trial h G language seed time bound n bits length
    exact ⟨x, y, produced, collision⟩
  rw [collisionSuccess_eq_univ_of_full_seeds h finder n (seed (4 * (n + 1) + 2)) full]
  exact measure_univ

end

end ComplexityOfGenerators
