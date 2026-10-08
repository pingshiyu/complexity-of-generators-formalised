import ComplexityOfGenerators.Simulation.BinaryOutputDecoder
import ComplexityOfGenerators.Proofs.NonemptyTrialBounds

/-!
# Native decoding in the binary collision reduction

The collision language in the main theorem is binary. Its generator can be
converted to the collision finder's ternary output format by the concrete
finite-control decoder, with no increase in runtime. The only index used below
is explicitly `4 * (n + 1) + 2`. The physical index adapter is implemented and
proved in `Simulation.VirtualIndexPolynomial`; `Proofs.BinaryCollisionFinder`
combines it with this decoder to establish cryptographic non-generability.
-/

namespace ComplexityOfGenerators

open Simulation

variable (h : HashFunction) (G : GeneratorFamily Bool)
variable (language : G.toUniformGenerators.language = h.binaryCollisionLanguage)
variable (seed time : PolynomialBound) (bound : G.toUniformGenerators.RunsInTime seed time)

include language in
/-- Every security parameter corresponds to a nonempty binary generator slice. -/
theorem binary_collision_generator_nonempty (n : ℕ) :
    (G.toUniformGenerators.layer (4 * (n + 1) + 2)).Nonempty := by
  rw [G.layer_eq_lengthSlice, language]
  exact h.binary_collision_slice_nonempty n

include language bound in
/-- The concrete output decoder preserves a bound on all finite tapes. -/
theorem binary_collision_decoder_timeBound (n : ℕ) :
    (binaryOutputDecoder G.machine).TimeBound (generatorData (4 * (n + 1) + 2))
      (time (4 * (n + 1) + 2)) := by
  apply binaryOutputDecoder_timeBound
  exact G.machine.generatorTimeBound_timeBound_of_nonempty _ _ _ (bound _)
    (binary_collision_generator_nonempty h G language n)

include language bound in
/-- Every full trial now produces the actual separated pair expected by the
security game. No ternary-language closure property is needed for decoding. -/
theorem binary_collision_decoder_full_trial (n : ℕ) (bits : BitString)
    (length : bits.length = seed (4 * (n + 1) + 2)) :
    ∃ x y : BitString, h.IsCollision n x y ∧
      (binaryOutputDecoder G.machine).Produces (generatorData (4 * (n + 1) + 2)) bits (encodePair x y) := by
  let size := 4 * (n + 1) + 2
  obtain ⟨word, produced⟩ := ((bound size).2 bits length).mpr
    (binary_collision_generator_nonempty h G language n)
  have nonempty : bits ≠ [] := by
    intro empty
    have positive := seed.positive (4 * (n + 1) + 2)
    simp [empty] at length
    omega
  have member : word ∈ G.toUniformGenerators.layer size := ⟨bits, nonempty, produced⟩
  rw [G.layer_eq_lengthSlice, language] at member
  obtain ⟨x, y, collision, rfl⟩ := h.binary_collision_member_parameter n word member.1 member.2
  exact ⟨x, y, collision, binaryOutputDecoder_produces G.machine _ bits _ produced⟩

include language bound in
/-- A time-sized tape suffices for a genuine collision, independently of the
minimum seed budget. This form accommodates simulators that consume extra choice
bits during administrative transitions. The actual output is already present
at the stated native clock, rather than merely at some unspecified later time. -/
theorem binary_collision_decoder_long_tape (n : ℕ) (bits : BitString)
    (long : time (4 * (n + 1) + 2) < bits.length) :
    ∃ x y : BitString, h.IsCollision n x y ∧
      (binaryOutputDecoder G.machine).run (generatorData (4 * (n + 1) + 2)) bits
        (time (4 * (n + 1) + 2)) = .halted (.accepted (encodePair x y)) := by
  let size := 4 * (n + 1) + 2
  have allTapes := G.machine.generatorTimeBound_timeBound_of_nonempty (generatorData size)
    (seed size) (time size) (bound size) (binary_collision_generator_nonempty h G language n)
  obtain ⟨word, produced⟩ := G.machine.accepts_at_timeBound_of_long_tape (generatorData size)
    (time size) (G.isGenerator size) allTapes bits long
  have nonempty : bits ≠ [] := by intro empty; simp [empty] at long
  have member : word ∈ G.toUniformGenerators.layer size := ⟨bits, nonempty, time size, produced⟩
  rw [G.layer_eq_lengthSlice, language] at member
  obtain ⟨x, y, collision, rfl⟩ := h.binary_collision_member_parameter n word member.1 member.2
  refine ⟨x, y, collision, ?_⟩
  rw [binaryOutputDecoder_run]
  change decodeOutputResult G.machine (G.machine.run (generatorData size) bits (time size)) = _
  rw [produced]
  simp [decodeOutputResult, decodeOutputOutcome]

/-- Numeric substitution is polynomial; this lemma does not by itself simulate
the change to the machine's physical unary index tape. -/
theorem binary_collision_reindexed_polynomial (p : PolynomialBound) :
    ∃ q : PolynomialBound, ∀ n, p (4 * (n + 1) + 2) ≤ q n := by
  let size : PolynomialBound := ⟨6, 1, by decide⟩
  refine ⟨p.comp size, fun n => ?_⟩
  apply le_trans ?_ (p.comp_le size n)
  change p.coefficient * (4 * (n + 1) + 2 + 1) ^ p.degree ≤
    p.coefficient * (size n + 1) ^ p.degree
  apply Nat.mul_le_mul_left
  apply pow_le_pow_left'
  simp [size, PolynomialBound.eval]
  omega

end ComplexityOfGenerators
