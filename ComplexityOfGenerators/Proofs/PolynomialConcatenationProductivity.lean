import ComplexityOfGenerators.Proofs.PolynomialConcatenationSupport

namespace ComplexityOfGenerators.Simulation.ConcatenationGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

omit [Fintype α] in
theorem offer_productive (previous candidate : Option (List α)) (replace : Bool)
    (available : (∃ word, previous = some word) ∨ ∃ word, candidate = some word) :
    ∃ word, offer previous candidate replace = some word := by
  cases previous <;> cases candidate <;> cases replace <;> simp_all [offer]

omit [Fintype α] in
theorem next_random_length (G H : Machine Unit Bool α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n j : ℕ) (p : Option (List α) × BitString) :
    (next G H leftSeed leftTime rightSeed rightTime n j p).2.length =
      p.2.length - blockSize leftSeed rightSeed n j := by
  simp [next, blockSize, Nat.sub_sub]

variable (G H : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (leftBound : G.toUniformGenerators.RunsInTime leftSeed leftTime)
    (rightBound : H.toUniformGenerators.RunsInTime rightSeed rightTime)

include leftBound rightBound

theorem next_productive (n j : ℕ) (p : Option (List α) × BitString)
    (full : blockSize leftSeed rightSeed n j ≤ p.2.length)
    (available : (∃ word, p.1 = some word) ∨
      (G.toUniformGenerators.layer j).Nonempty ∧ (H.toUniformGenerators.layer (n - j)).Nonempty) :
    ∃ word, (next G.machine H.machine leftSeed leftTime rightSeed rightTime n j p).1 = some word := by
  apply offer_productive
  rcases available with existing | ⟨left, right⟩
  · exact Or.inl existing
  · have leftLength : (p.2.take (leftSeed j)).length = leftSeed j := by
      simp only [List.length_take]; unfold blockSize at full; omega
    have rightLength : ((p.2.drop (leftSeed j)).take (rightSeed (n - j))).length = rightSeed (n - j) := by
      simp only [List.length_take, List.length_drop]; unfold blockSize at full; omega
    obtain ⟨u, hu⟩ := UnionGenerator.sourceValue_full G.toUniformGenerators leftSeed leftTime leftBound j _ leftLength left
    obtain ⟨v, hv⟩ := UnionGenerator.sourceValue_full H.toUniformGenerators rightSeed rightTime rightBound (n - j) _ rightLength right
    exact Or.inr ⟨u ++ v, by simp [pairValue, hu, hv]⟩

theorem fold_productive (n : ℕ) (splits : List ℕ) (p : Option (List α) × BitString)
    (full : blocksSize leftSeed rightSeed n splits ≤ p.2.length)
    (available : (∃ word, p.1 = some word) ∨
      ∃ j ∈ splits, (G.toUniformGenerators.layer j).Nonempty ∧ (H.toUniformGenerators.layer (n - j)).Nonempty) :
    ∃ word, (splits.foldl (fun p j => next G.machine H.machine leftSeed leftTime rightSeed rightTime n j p) p).1 = some word := by
  induction splits generalizing p with
  | nil => simpa using available
  | cons j rest ih =>
    have costs : blockSize leftSeed rightSeed n j + blocksSize leftSeed rightSeed n rest ≤ p.2.length := by
      simpa only [blocksSize, List.map_cons, List.sum_cons] using full
    let q := next G.machine H.machine leftSeed leftTime rightSeed rightTime n j p
    have remainder : blocksSize leftSeed rightSeed n rest ≤ q.2.length := by
      dsimp only [q]
      rw [next_random_length]
      omega
    apply ih q remainder
    rcases available with previous | ⟨k, occurs, viable⟩
    · exact Or.inl (next_productive G H leftSeed leftTime rightSeed rightTime leftBound rightBound n j p
        (by omega) (Or.inl previous))
    · rcases List.mem_cons.mp occurs with equal | occurs
      · subst k
        exact Or.inl (next_productive G H leftSeed leftTime rightSeed rightTime leftBound rightBound n j p
          (by omega) (Or.inr viable))
      · exact Or.inr ⟨k, occurs, viable⟩

theorem algorithm_productive (n : ℕ) (bits : BitString)
    (length : bits.length = concatSeed leftSeed rightSeed n)
    (nonempty : (lengthSlice
      (IndexedSupport.concat G.toUniformGenerators.language H.toUniformGenerators.language) n).Nonempty) :
    ∃ word, algorithm G.machine H.machine leftSeed leftTime rightSeed rightTime n bits = some word := by
  obtain ⟨_, ⟨u, left, v, right, rfl⟩, lengthSum⟩ := nonempty
  have sizes : u.length + v.length = n := by simpa using lengthSum
  have leftLayer : u ∈ G.toUniformGenerators.layer u.length := by
    rw [G.layer_eq_lengthSlice]; exact ⟨left, rfl⟩
  have rightLayer : v ∈ H.toUniformGenerators.layer (n - u.length) := by
    rw [H.layer_eq_lengthSlice]; exact ⟨right, by omega⟩
  exact fold_productive G H leftSeed leftTime rightSeed rightTime leftBound rightBound n (List.range (n + 1)) (none, bits)
    (by rw [length]; exact totalBlocks_le leftSeed rightSeed n)
    (Or.inr ⟨u.length, by simp; omega, ⟨u, leftLayer⟩, ⟨v, rightLayer⟩⟩)

end
end ComplexityOfGenerators.Simulation.ConcatenationGenerator
