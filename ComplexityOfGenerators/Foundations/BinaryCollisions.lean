import ComplexityOfGenerators.Proofs.CryptographicReduction

/-!
# A fixed binary encoding of the collision language

The main separation theorem uses binary languages, whereas a collision finder
outputs two bitstrings separated by a third symbol. Two-bit blocks encode these
three symbols injectively. The unused block `11` and truncated blocks are
rejected by the decoder. No complexity-class closure is assumed here.
-/

namespace ComplexityOfGenerators

/-- `00` and `01` encode the two bits; `10` is the reserved separator. -/
def pairSymbolBits : PairSymbol → BitString
  | .bit bit => [false, bit]
  | .separator => [true, false]

def binaryPairWord (word : List PairSymbol) : BitString := word.flatMap pairSymbolBits

def readBinaryPairWord : BitString → Option (List PairSymbol)
  | [] => some []
  | false :: bit :: tail => (readBinaryPairWord tail).map (PairSymbol.bit bit :: ·)
  | true :: false :: tail => (readBinaryPairWord tail).map (PairSymbol.separator :: ·)
  | _ => none

@[simp] theorem readBinaryPairWord_encode (word : List PairSymbol) :
    readBinaryPairWord (binaryPairWord word) = some word := by
  induction word with
  | nil => rfl
  | cons symbol tail ih =>
      cases symbol <;> simp [binaryPairWord, pairSymbolBits, readBinaryPairWord] at ih ⊢
      all_goals exact ih

@[simp] theorem binaryPairWord_length (word : List PairSymbol) :
    (binaryPairWord word).length = 2 * word.length := by
  induction word with
  | nil => rfl
  | cons symbol tail ih =>
      cases symbol <;> simp [binaryPairWord, pairSymbolBits] at ih ⊢ <;> omega

/-- Decoding admits exactly the canonical block encodings. -/
theorem binaryPairWord_of_decoded {bits : BitString} {word : List PairSymbol}
    (decoded : readBinaryPairWord bits = some word) : binaryPairWord word = bits := by
  induction bits using readBinaryPairWord.induct generalizing word with
  | case1 =>
      simp only [readBinaryPairWord, Option.some.injEq] at decoded
      rw [← decoded]
      rfl
  | case2 bit tail ih =>
      cases rest : readBinaryPairWord tail with
      | none => simp [readBinaryPairWord, rest] at decoded
      | some output =>
          simp only [readBinaryPairWord, rest, Option.map_some, Option.some.injEq] at decoded
          subst word
          simpa [binaryPairWord, pairSymbolBits] using
            congrArg (fun xs : BitString => false :: bit :: xs) (ih rest)
  | case3 tail ih =>
      cases rest : readBinaryPairWord tail with
      | none => simp [readBinaryPairWord, rest] at decoded
      | some output =>
          simp only [readBinaryPairWord, rest, Option.map_some, Option.some.injEq] at decoded
          subst word
          simpa [binaryPairWord, pairSymbolBits] using
            congrArg (fun xs : BitString => true :: false :: xs) (ih rest)
  | case4 => simp [readBinaryPairWord] at decoded

theorem binaryPairWord_injective : Function.Injective binaryPairWord := by
  intro x y equal
  have decoded := congrArg readBinaryPairWord equal
  simpa using decoded

/-- Binary version of the paper's collision language, with malformed inputs
excluded rather than assigned an arbitrary collision interpretation. -/
def HashFunction.binaryCollisionLanguage (h : HashFunction) : Language Bool :=
  {bits | ∃ word ∈ h.collisionLanguage, bits = binaryPairWord word}

theorem HashFunction.binaryCollisionLanguage_iff (h : HashFunction) (bits : BitString) :
    bits ∈ h.binaryCollisionLanguage ↔
      ∃ word, readBinaryPairWord bits = some word ∧ word ∈ h.collisionLanguage := by
  constructor
  · rintro ⟨word, member, rfl⟩
    exact ⟨word, readBinaryPairWord_encode word, member⟩
  · rintro ⟨word, decoded, member⟩
    exact ⟨word, member, (binaryPairWord_of_decoded decoded).symm⟩

/-- Compression forces a nonempty binary collision slice at every parameter. -/
theorem HashFunction.binary_collision_slice_nonempty (h : HashFunction) (n : ℕ) :
    (lengthSlice h.binaryCollisionLanguage (4 * (n + 1) + 2)).Nonempty := by
  obtain ⟨word, member, length⟩ := h.collision_slice_nonempty n
  exact ⟨binaryPairWord word, ⟨word, member, rfl⟩, by simp [length]; omega⟩

/-- Output length recovers the intended hash parameter after binary encoding. -/
theorem HashFunction.binary_collision_member_parameter (h : HashFunction) (n : ℕ)
    (bits : BitString) (member : bits ∈ h.binaryCollisionLanguage)
    (length : bits.length = 4 * (n + 1) + 2) :
    ∃ x y : BitString, h.IsCollision n x y ∧ bits = binaryPairWord (encodePair x y) := by
  obtain ⟨word, collision, rfl⟩ := member
  have wordLength : word.length = 2 * (n + 1) + 1 := by
    rw [binaryPairWord_length] at length
    omega
  obtain ⟨x, y, genuine, rfl⟩ := h.collision_member_parameter n word collision wordLength
  exact ⟨x, y, genuine, rfl⟩

end ComplexityOfGenerators
