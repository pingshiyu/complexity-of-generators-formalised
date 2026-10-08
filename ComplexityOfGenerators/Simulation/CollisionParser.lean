import ComplexityOfGenerators.Simulation.CollisionParserX
import ComplexityOfGenerators.Simulation.CollisionParserY

namespace ComplexityOfGenerators.Simulation

/-- Pure specification of the validation performed before running a hash. -/
def collisionParse (word : BitString) : Option (BitString × BitString) := do
  let (x, rest) ← splitCollisionInput word
  let y ← readCollisionBits rest
  if x ≠ [] ∧ x.length = y.length ∧ x ≠ y then some (x, y) else none

theorem readCollisionBits_sound (word xs : BitString) (h : readCollisionBits word = some xs) :
    word = collisionBits xs := by
  induction word using readCollisionBits.induct generalizing xs with
  | case1 =>
      have eq : xs = [] := by simpa [readCollisionBits, eq_comm] using h
      subst xs
      rfl
  | case2 b word ih =>
      cases read : readCollisionBits word with
      | none => simp [readCollisionBits, read] at h
      | some tail =>
          have eq : b :: tail = xs := by simpa [readCollisionBits, read] using h
          subst xs
          simp [ih tail read]
  | case3 => simp [readCollisionBits] at h

theorem collisionParse_sound (word x y : BitString) (h : collisionParse word = some (x, y)) :
    word = collisionBits x ++ true :: false :: collisionBits y ∧
      x ≠ [] ∧ x.length = y.length ∧ x ≠ y := by
  cases split : splitCollisionInput word with
  | none => simp [collisionParse, split] at h
  | some pair =>
      obtain ⟨a, rest⟩ := pair
      cases read : readCollisionBits rest with
      | none => simp [collisionParse, split, read] at h
      | some b =>
          by_cases valid : a ≠ [] ∧ a.length = b.length ∧ a ≠ b
          · have same : (a, b) = (x, y) := by simpa [collisionParse, split, read, valid] using h
            cases same
            exact ⟨by rw [splitCollisionInput_sound word x rest split, readCollisionBits_sound rest y read], valid⟩
          · simp [collisionParse, split, read, valid] at h

theorem collisionParse_encoded (x y : BitString)
    (valid : x ≠ [] ∧ x.length = y.length ∧ x ≠ y) :
    collisionParse (collisionBits x ++ true :: false :: collisionBits y) = some (x, y) := by
  simp [collisionParse, splitCollisionInput_encoded, readCollisionBits_encoded, valid]

theorem collisionBits_pair (x y : BitString) :
    binaryPairWord (encodePair x y) = collisionBits x ++ true :: false :: collisionBits y := by
  simp [binaryPairWord, encodePair, List.flatMap_map, Function.comp_def, pairSymbolBits, collisionBits]

theorem collisionParse_of_member (h : HashFunction) (word : BitString) (member : word ∈ h.binaryCollisionLanguage) :
    ∃ x y, collisionParse word = some (x, y) ∧ h.IsCollision (x.length - 1) x y := by
  obtain ⟨pair, ⟨n, x, y, collision, rfl⟩, rfl⟩ := member
  have lengths : x.length = n + 1 ∧ y.length = n + 1 ∧ x ≠ y := by
    obtain ⟨a, b, rfl, rfl, distinct, _⟩ := collision
    simp [distinct]
  refine ⟨x, y, ?_, by simpa [lengths.1] using collision⟩
  rw [collisionBits_pair]
  apply collisionParse_encoded
  exact ⟨by intro empty; simp [empty] at lengths, by omega, lengths.2.2⟩

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (M : Machine Bool Bool Bool)

def CollisionParseResult (word : BitString) (t : ℕ) : Prop :=
  match collisionParse word with
  | none => (collisionBank M).Executes word (collisionBank M).initialConfiguration t false
  | some (x, y) => (collisionBank M).Steps word (collisionBank M).initialConfiguration t
      (collisionParsedConfiguration M word x y)

/-- Total parsing from blank tapes. Rejection includes every malformed encoding,
empty first preimage, unequal length, and equal-preimage case. -/
theorem collision_parse (word : BitString) :
    ∃ t, t ≤ 12 * (word.length + 1) ∧ CollisionParseResult M word t := by
  obtain ⟨s, cost₁, result₁⟩ := collision_parse_x M word [] word (by simp)
  simp only [List.length_nil, Nat.add_zero] at cost₁
  cases split : splitCollisionInput word with
  | none =>
      refine ⟨s, by omega, ?_⟩
      simpa [CollisionParseResult, collisionParse, split, CollisionXResult] using result₁
  | some pair =>
      obtain ⟨x, rest⟩ := pair
      have encoding := splitCollisionInput_sound word x rest split
      have sizes : 2 * x.length + (rest.length + 2) = word.length := by simp [encoding]
      by_cases empty : x = []
      · subst x
        refine ⟨s, by omega, ?_⟩
        have rejected : (collisionBank M).Executes word (collisionBank M).initialConfiguration s false := by
          simpa [CollisionXResult, split] using result₁
        cases read : readCollisionBits rest <;>
          simpa [CollisionParseResult, collisionParse, split, read] using rejected
      · have path : (collisionBank M).Steps word (collisionBank M).initialConfiguration s
            (collisionYConfiguration M x []) := by simpa [CollisionXResult, split, empty] using result₁
        obtain ⟨u, cost₂, result₂⟩ := collision_parse_y M word x [] rest (by simp) (by simpa using encoding)
        refine ⟨s + u, by omega, ?_⟩
        cases read : readCollisionBits rest with
        | none =>
            have rejected : (collisionBank M).Executes word (collisionYConfiguration M x []) u false := by
              simpa [CollisionYResult, read] using result₂
            simpa [CollisionParseResult, collisionParse, split, read] using path.executes (collisionBank M) rejected
        | some y =>
            by_cases valid : x.length = y.length ∧ x ≠ y
            · have restPath : (collisionBank M).Steps word (collisionYConfiguration M x []) u
                  (collisionParsedConfiguration M word x y) := by
                simpa [CollisionYResult, read, valid] using result₂
              simpa [CollisionParseResult, collisionParse, split, read, empty, valid] using path.trans (collisionBank M) restPath
            · have rejected : (collisionBank M).Executes word (collisionYConfiguration M x []) u false := by
                simpa [CollisionYResult, read, valid] using result₂
              simpa [CollisionParseResult, collisionParse, split, read, empty, valid] using path.executes (collisionBank M) rejected

end
end ComplexityOfGenerators.Simulation
