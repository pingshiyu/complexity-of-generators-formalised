import ComplexityOfGenerators.Foundations.BinaryCollisions
import ComplexityOfGenerators.Simulation.ClockProgress

/-!
# Correctness of the collision-verification algorithm

This executable specification parses the binary pair, checks the lengths and
inequality of the preimages, and evaluates the two native hash computations at
their proved deadlines. It decides exactly the binary collision language,
including rejection of malformed words. `PolynomialCollisionDecision` supplies
the native decider and its polynomial simulation bound; evaluating `Machine.run`
in this specification is not counted as one native machine instruction.
-/

namespace ComplexityOfGenerators

@[simp] theorem bitsWord_inj {n : ℕ} (a b : Bits n) : bitsWord a = bitsWord b ↔ a = b := by
  simp [bitsWord]

theorem exists_bitsWord_of_length (word : BitString) (n : ℕ) (length : word.length = n) :
    ∃ bits : Bits n, bitsWord bits = word := by
  refine ⟨fun i => word[i.val]'(by omega), ?_⟩
  apply List.ext_getElem
  · simpa using length.symm
  · intro i hi hj
    simp [bitsWord]

def HashFunction.nativeCollisionCheck (h : HashFunction) (n : ℕ) (x y : BitString) : Bool :=
  if x.length = n + 1 ∧ y.length = n + 1 ∧ x ≠ y then
    match (h.implementation.run {input := x, index := n} [] (h.time n)).acceptedWord,
      (h.implementation.run {input := y, index := n} [] (h.time n)).acceptedWord with
    | some hx, some hy => decide (hx = hy)
    | _, _ => false
  else false

theorem HashFunction.run_at_hash_bound (h : HashFunction) (n : ℕ) (x : Bits (n + 1)) :
    h.implementation.run {input := bitsWord x, index := n} [] (h.time n) =
      .halted (.accepted (bitsWord (h.hash n x))) :=
  h.implementation.produces_at_bound _ [] (h.time n) _ (h.timeBound n x []) (h.computes n x)

theorem HashFunction.nativeCollisionCheck_correct (h : HashFunction) (n : ℕ) (x y : BitString) :
    h.nativeCollisionCheck n x y = true ↔ h.IsCollision n x y := by
  by_cases valid : x.length = n + 1 ∧ y.length = n + 1
  · obtain ⟨a, rfl⟩ := exists_bitsWord_of_length x (n + 1) valid.1
    obtain ⟨b, rfl⟩ := exists_bitsWord_of_length y (n + 1) valid.2
    simp [HashFunction.nativeCollisionCheck, h.run_at_hash_bound, RunState.acceptedWord,
      Outcome.acceptedWord, HashFunction.IsCollision]
  · have invalid : ¬ h.IsCollision n x y := by
      rintro ⟨a, b, rfl, rfl, _, _⟩
      exact valid (by simp)
    have guard : ¬ (x.length = n + 1 ∧ y.length = n + 1 ∧ x ≠ y) := by tauto
    simp [HashFunction.nativeCollisionCheck, guard, invalid]

def HashFunction.binaryCollisionCheck (h : HashFunction) (bits : BitString) : Bool :=
  match readBinaryPairWord bits >>= decodePair with
  | none => false
  | some (x, y) => h.nativeCollisionCheck (x.length - 1) x y

theorem HashFunction.binaryCollisionCheck_correct (h : HashFunction) (bits : BitString) :
    h.binaryCollisionCheck bits = true ↔ bits ∈ h.binaryCollisionLanguage := by
  constructor
  · intro accepted
    cases read : readBinaryPairWord bits with
    | none => simp [HashFunction.binaryCollisionCheck, read] at accepted
    | some word =>
        cases parse : decodePair word with
        | none => simp [HashFunction.binaryCollisionCheck, read, parse] at accepted
        | some pair =>
            have collision : h.IsCollision (pair.1.length - 1) pair.1 pair.2 := by
              apply (h.nativeCollisionCheck_correct _ _ _).mp
              simpa [HashFunction.binaryCollisionCheck, read, parse] using accepted
            refine ⟨word, ⟨_, pair.1, pair.2, collision, decodePair_sound word pair.1 pair.2 parse⟩,
              (binaryPairWord_of_decoded read).symm⟩
  · rintro ⟨word, ⟨n, x, y, collision, rfl⟩, rfl⟩
    have length : x.length = n + 1 := by
      obtain ⟨a, b, rfl, _, _, _⟩ := collision
      simp
    simpa [HashFunction.binaryCollisionCheck, length] using
      (h.nativeCollisionCheck_correct n x y).mpr collision

end ComplexityOfGenerators
