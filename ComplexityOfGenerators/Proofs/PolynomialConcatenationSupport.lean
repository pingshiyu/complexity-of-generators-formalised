import ComplexityOfGenerators.Simulation.ConcatenationGenerator.Components
import ComplexityOfGenerators.Proofs.PolynomialUnionSupport
import ComplexityOfGenerators.Foundations.IndexedSupportClosure

namespace ComplexityOfGenerators.Simulation.ConcatenationGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

omit [Fintype α] in
theorem pairValue_some {left right : Option (List α)} {word : List α}
    (output : pairValue left right = some word) :
    ∃ u v, left = some u ∧ right = some v ∧ u ++ v = word := by
  cases left with
  | none => simp [pairValue] at output
  | some u =>
    cases right with
    | none => simp [pairValue] at output
    | some v => exact ⟨u, v, rfl, rfl, Option.some.inj output⟩

omit [Fintype α] in
theorem offer_some {previous candidate : Option (List α)} {word : List α} (replace : Bool)
    (output : offer previous candidate replace = some word) :
    previous = some word ∨ candidate = some word := by
  unfold offer at output
  split at output
  · exact Or.inr output
  · split at output
    · exact (UnionGenerator.or_some_cases output).symm
    · exact Or.inl output

omit [Fintype α] in
def blockSize (leftSeed rightSeed : PolynomialBound) (n j : ℕ) : ℕ :=
  leftSeed j + rightSeed (n - j) + 1

def concatSeed (leftSeed rightSeed : PolynomialBound) : PolynomialBound :=
  (⟨1, 1, by decide⟩ : PolynomialBound).mul (UnionGenerator.unionSeed leftSeed rightSeed)

theorem blockSize_le (leftSeed rightSeed : PolynomialBound) (n j : ℕ) (split : j ≤ n) :
    blockSize leftSeed rightSeed n j ≤ UnionGenerator.unionSeed leftSeed rightSeed n := by
  exact (Nat.add_le_add_right (Nat.add_le_add (leftSeed.monotone split)
    (rightSeed.monotone (Nat.sub_le n j))) 1).trans (UnionGenerator.unionSeed_lower leftSeed rightSeed n)

def blocksSize (leftSeed rightSeed : PolynomialBound) (n : ℕ) (splits : List ℕ) : ℕ :=
  (splits.map (blockSize leftSeed rightSeed n)).sum

theorem blocksSize_le (leftSeed rightSeed : PolynomialBound) (n : ℕ) (splits : List ℕ)
    (indices : ∀ j ∈ splits, j ≤ n) :
    blocksSize leftSeed rightSeed n splits ≤ splits.length * UnionGenerator.unionSeed leftSeed rightSeed n := by
  induction splits with
  | nil => simp [blocksSize]
  | cons j rest ih =>
    have head := blockSize_le leftSeed rightSeed n j (indices j (by simp))
    have tail := ih (by intro i hi; exact indices i (by simp [hi]))
    simp only [blocksSize, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem totalBlocks_le (leftSeed rightSeed : PolynomialBound) (n : ℕ) :
    blocksSize leftSeed rightSeed n (List.range (n + 1)) ≤ concatSeed leftSeed rightSeed n := by
  have bound := blocksSize_le leftSeed rightSeed n (List.range (n + 1))
    (by intro j member; have := List.mem_range.mp member; omega)
  calc
    _ ≤ (n + 1) * UnionGenerator.unionSeed leftSeed rightSeed n := by
      simpa only [List.length_range] using bound
    _ = concatSeed leftSeed rightSeed n := by
      simp [concatSeed, PolynomialBound.mul, PolynomialBound.eval, pow_add]
      ring

omit [Fintype α] in
theorem next_blocks (G H : Machine Unit Bool α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (previous : Option (List α)) (left right : BitString) (coin : Bool) (tail : BitString)
    (leftLength : left.length = leftSeed j) (rightLength : right.length = rightSeed (n - j)) :
    next G H leftSeed leftTime rightSeed rightTime n j (previous, left ++ right ++ [coin] ++ tail) =
      (offer previous (pairValue (UnionGenerator.sourceValue G leftTime j left)
        (UnionGenerator.sourceValue H rightTime (n - j) right)) coin, tail) := by
  cases coin <;>
    simp [next, List.append_assoc, List.drop_append, ← leftLength, ← rightLength] <;> omega

theorem next_sound (G H : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (index : j ≤ n) (p : Option (List α) × BitString)
    (valid : ∀ word, p.1 = some word → word ∈ lengthSlice
      (IndexedSupport.concat G.toUniformGenerators.language H.toUniformGenerators.language) n) :
    ∀ word, (next G.machine H.machine leftSeed leftTime rightSeed rightTime n j p).1 = some word →
      word ∈ lengthSlice (IndexedSupport.concat G.toUniformGenerators.language H.toUniformGenerators.language) n := by
  intro word output
  rcases offer_some _ output with previous | candidate
  · exact valid word previous
  · obtain ⟨u, v, left, right, rfl⟩ := pairValue_some candidate
    have leftMember := UnionGenerator.sourceValue_mem G.toUniformGenerators leftTime j _ u left
    have rightMember := UnionGenerator.sourceValue_mem H.toUniformGenerators rightTime (n - j) _ v right
    refine ⟨⟨u, ⟨j, leftMember⟩, v, ⟨n - j, rightMember⟩, rfl⟩, ?_⟩
    simp only [List.length_append, G.outputLength j u leftMember,
      H.outputLength (n - j) v rightMember]
    omega

theorem fold_sound (G H : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (splits : List ℕ) (indices : ∀ j ∈ splits, j ≤ n)
    (p : Option (List α) × BitString)
    (valid : ∀ word, p.1 = some word → word ∈ lengthSlice
      (IndexedSupport.concat G.toUniformGenerators.language H.toUniformGenerators.language) n) :
    ∀ word, (splits.foldl (fun p j => next G.machine H.machine leftSeed leftTime rightSeed rightTime n j p) p).1 = some word →
      word ∈ lengthSlice (IndexedSupport.concat G.toUniformGenerators.language H.toUniformGenerators.language) n := by
  induction splits generalizing p with
  | nil => exact valid
  | cons j rest ih =>
    exact ih (by intro i hi; exact indices i (by simp [hi])) _
      (next_sound G H leftSeed leftTime rightSeed rightTime n j (indices j (by simp)) p valid)

theorem algorithm_sound (G H : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (bits : BitString) (word : List α)
    (output : algorithm G.machine H.machine leftSeed leftTime rightSeed rightTime n bits = some word) :
    word ∈ lengthSlice (IndexedSupport.concat G.toUniformGenerators.language H.toUniformGenerators.language) n :=
  fold_sound G H leftSeed leftTime rightSeed rightTime n (List.range (n + 1))
    (by intro j member; have := List.mem_range.mp member; omega) (none, bits)
    (by intro w impossible; cases impossible) word output

end
end ComplexityOfGenerators.Simulation.ConcatenationGenerator
