import ComplexityOfGenerators.Simulation.CollisionParser
import ComplexityOfGenerators.Simulation.CollisionHashPair
import ComplexityOfGenerators.Proofs.BoundedNondeterministicRecognition

/-!
# Polynomial-time decision of the collision language

The witness is a concrete native finite-control machine. It loads and checks
the canonical binary encoding, constructs the unary hash index, executes both
given native hash implementations, and compares their outputs. The proof
includes all parsing, initialization, simulation, and tape-reset costs. There
is no closure assumption about `P`, and no computational field is added to the
cryptographic assumption.
-/

namespace ComplexityOfGenerators

open Simulation

noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem HashFunction.parsed_collision_correct (h : HashFunction) (word : BitString)
    (n : ℕ) (a b : Bits (n + 1))
    (parsed : collisionParse word = some (bitsWord a, bitsWord b)) :
    decide (h.hash n a = h.hash n b) = true ↔ word ∈ h.binaryCollisionLanguage := by
  obtain ⟨encoding, _, _, distinct⟩ := collisionParse_sound word (bitsWord a) (bitsWord b) parsed
  constructor
  · intro equal
    have hashEqual : h.hash n a = h.hash n b := of_decide_eq_true equal
    refine ⟨encodePair (bitsWord a) (bitsWord b),
      ⟨n, bitsWord a, bitsWord b, ⟨a, b, rfl, rfl, ?_, hashEqual⟩, rfl⟩, ?_⟩
    · intro same
      exact distinct (congrArg bitsWord same)
    · rw [collisionBits_pair]
      exact encoding
  · intro member
    obtain ⟨x, y, other, collision⟩ := collisionParse_of_member h word member
    have same := Option.some.inj (parsed.symm.trans other)
    have hx : x = bitsWord a := (congrArg Prod.fst same).symm
    have hy : y = bitsWord b := (congrArg Prod.snd same).symm
    subst x y
    have collision' : h.IsCollision n (bitsWord a) (bitsWord b) := by
      simpa only [bitsWord_length, Nat.add_sub_cancel] using collision
    have pair : a ≠ b ∧ h.hash n a = h.hash n b := by
      simpa [HashFunction.IsCollision] using collision'
    exact decide_eq_true pair.2

/-- The collision language appearing in the separation proof is in the native
deterministic class `P`, under exactly the implementation/time fields already
present in `HashFunction`. Collision resistance is not needed for this fact. -/
theorem HashFunction.binaryCollisionLanguage_mem_p (h : HashFunction) :
    h.binaryCollisionLanguage ∈ P Bool := by
  let poly := 12 * (Polynomial.X + 1) + 12 * h.time.asPolynomial + 5 * Polynomial.X + 10
  let time := PolynomialBound.ofPolynomial poly
  have budget (n : ℕ) : 12 * (n + 1) + 12 * h.time n + 5 * n + 10 ≤ time n := by
    have bound := PolynomialBound.eval_le_ofPolynomial poly n
    simpa [poly] using bound
  apply mem_p_of_tapeBank (collisionBank h.implementation) h.binaryCollisionLanguage time
  intro word
  obtain ⟨s, cost, parsedRun⟩ := collision_parse h.implementation word
  cases parsed : collisionParse word with
  | none =>
      refine ⟨s, false, cost.trans (by have := budget word.length; omega), ?_, ?_⟩
      · simpa [CollisionParseResult, parsed] using parsedRun
      · simp only [Bool.false_eq_true, false_iff]
        intro member
        obtain ⟨x, y, somePair, _⟩ := collisionParse_of_member h word member
        rw [parsed] at somePair
        cases somePair
  | some pair =>
      obtain ⟨x, y⟩ := pair
      obtain ⟨encoding, positive, lengths, distinct⟩ := collisionParse_sound word x y parsed
      have nonzero : 0 < x.length := List.length_pos_iff.mpr positive
      let n := x.length - 1
      have xlength : x.length = n + 1 := by dsimp [n]; omega
      have ylength : y.length = n + 1 := lengths ▸ xlength
      obtain ⟨a, ha⟩ := exists_bitsWord_of_length x (n + 1) xlength
      obtain ⟨b, hb⟩ := exists_bitsWord_of_length y (n + 1) ylength
      have size : n ≤ word.length := by
        have wordLength : word.length = 2 * x.length + 2 + 2 * y.length := by simp [encoding]; omega
        omega
      have boundedHash := PolynomialBound.monotone h.time size
      obtain ⟨u, hashCost, hashRun⟩ := collision_hash_pair h word n a b
      have path : (collisionBank h.implementation).Steps word
          (collisionBank h.implementation).initialConfiguration s
          (collisionParsedConfiguration h.implementation word (bitsWord a) (bitsWord b)) := by
        simpa [CollisionParseResult, parsed, ha, hb] using parsedRun
      refine ⟨s + u, decide (h.hash n a = h.hash n b), ?_, path.executes _ hashRun, ?_⟩
      · have bound := budget word.length
        omega
      · apply h.parsed_collision_correct word n a b
        simpa [ha, hb] using parsed

end
end ComplexityOfGenerators
