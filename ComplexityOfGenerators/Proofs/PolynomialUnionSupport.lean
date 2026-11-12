import ComplexityOfGenerators.Simulation.UnionGenerator.Components
import ComplexityOfGenerators.Foundations.BoundedGeneration

/-! Support and full-budget productivity of the concrete two-source union
controller. All source calls are bounded native executions. -/

namespace ComplexityOfGenerators.Simulation.UnionGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

omit [Fintype α] in
theorem sourceValue_eq_some_iff (M : Machine Unit Bool α) (time : PolynomialBound)
    (n : ℕ) (bits : BitString) (word : List α) :
    sourceValue M time n bits = some word ↔
      M.run (generatorData n) bits (time n) = .halted (.accepted word) := by
  unfold sourceValue
  cases M.run (generatorData n) bits (time n) with
  | running c => simp [RunState.acceptedWord]
  | halted outcome => cases outcome <;> simp [RunState.acceptedWord, Outcome.acceptedWord]

omit [Fintype α] in
theorem sourceValue_mem (G : UniformGenerators α) (time : PolynomialBound)
    (n : ℕ) (bits : BitString) (word : List α)
    (output : sourceValue G.machine time n bits = some word) : word ∈ G.layer n := by
  exact ⟨bits ++ [false], by simp, G.machine.produces_append _ bits [false] word
    ⟨time n, (sourceValue_eq_some_iff G.machine time n bits word).mp output⟩⟩

theorem or_some_cases {β : Type} {left right : Option β} {x : β}
    (output : left.or right = some x) : left = some x ∨ right = some x := by
  cases left with
  | none => exact Or.inr output
  | some y => exact Or.inl output

theorem value_member (G H : UniformGenerators α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (bits : BitString) (word : List α)
    (output : value G.machine H.machine leftSeed leftTime rightSeed rightTime n bits = some word) :
    word ∈ G.layer n ∪ H.layer n := by
  unfold value at output
  split at output
  · rcases or_some_cases output with right | left
    · exact Or.inr (sourceValue_mem H rightTime n _ word right)
    · exact Or.inl (sourceValue_mem G leftTime n _ word left)
  · rcases or_some_cases output with left | right
    · exact Or.inl (sourceValue_mem G leftTime n _ word left)
    · exact Or.inr (sourceValue_mem H rightTime n _ word right)

theorem value_sound (G H : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (bits : BitString) (word : List α)
    (output : value G.machine H.machine leftSeed leftTime rightSeed rightTime n bits = some word) :
    word ∈ lengthSlice (G.toUniformGenerators.language ∪ H.toUniformGenerators.language) n := by
  rcases value_member G.toUniformGenerators H.toUniformGenerators leftSeed leftTime rightSeed rightTime
      n bits word output with left | right
  · exact ⟨Or.inl ⟨n, left⟩, G.outputLength n word left⟩
  · exact ⟨Or.inr ⟨n, right⟩, H.outputLength n word right⟩

/-- The collected seed leaves one selector bit after both source blocks. -/
def unionSeed (left right : PolynomialBound) : PolynomialBound :=
  (left.add right).add ⟨1, 0, by decide⟩

theorem unionSeed_lower (left right : PolynomialBound) (n : ℕ) :
    left n + right n + 1 ≤ unionSeed left right n := by
  exact (Nat.add_le_add_right (left.add_le right n) 1).trans
    (by simpa [unionSeed, PolynomialBound.eval] using
      (left.add right).add_le ⟨1, 0, by decide⟩ n)

omit [Fintype α] in
theorem value_blocks (G H : Machine Unit Bool α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (left right : BitString) (coin : Bool) (tail : BitString)
    (leftLength : left.length = leftSeed n) (rightLength : right.length = rightSeed n) :
    value G H leftSeed leftTime rightSeed rightTime n (left ++ right ++ [coin] ++ tail) =
      if coin then (sourceValue H rightTime n right).or (sourceValue G leftTime n left)
      else (sourceValue G leftTime n left).or (sourceValue H rightTime n right) := by
  simp [value, List.append_assoc, List.drop_append, ← leftLength, ← rightLength]

theorem value_complete (G H : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (leftBound : G.toUniformGenerators.RunsInTime leftSeed leftTime)
    (rightBound : H.toUniformGenerators.RunsInTime rightSeed rightTime)
    (n : ℕ) (word : List α)
    (member : word ∈ lengthSlice (G.toUniformGenerators.language ∪ H.toUniformGenerators.language) n) :
    ∃ bits, bits.length = unionSeed leftSeed rightSeed n ∧
      value G.machine H.machine leftSeed leftTime rightSeed rightTime n bits = some word := by
  let padding := List.replicate (unionSeed leftSeed rightSeed n - (leftSeed n + rightSeed n + 1)) false
  have size := unionSeed_lower leftSeed rightSeed n
  have leftLayer : word ∈ G.toUniformGenerators.language → word ∈ G.toUniformGenerators.layer n := by
    intro yes
    rw [G.layer_eq_lengthSlice]
    exact ⟨yes, member.2⟩
  have rightLayer : word ∈ H.toUniformGenerators.language → word ∈ H.toUniformGenerators.layer n := by
    intro yes
    rw [H.layer_eq_lengthSlice]
    exact ⟨yes, member.2⟩
  rcases member.1 with left | right
  · obtain ⟨chosen, length, run⟩ := (G.machine.generatedLanguage_iff_budget_seed _ _ _
      (leftSeed.positive n) (leftBound n) word).mp (leftLayer left)
    let other := List.replicate (rightSeed n) false
    refine ⟨chosen ++ other ++ [false] ++ padding, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, length, other, padding, List.length_replicate]
      omega
    · rw [value_blocks G.machine H.machine leftSeed leftTime rightSeed rightTime n chosen other false padding
        length (by simp [other])]
      simp [sourceValue, run, RunState.acceptedWord, Outcome.acceptedWord]
  · obtain ⟨chosen, length, run⟩ := (H.machine.generatedLanguage_iff_budget_seed _ _ _
      (rightSeed.positive n) (rightBound n) word).mp (rightLayer right)
    let other := List.replicate (leftSeed n) false
    refine ⟨other ++ chosen ++ [true] ++ padding, ?_, ?_⟩
    · simp only [List.length_append, List.length_singleton, length, other, padding, List.length_replicate]
      omega
    · rw [value_blocks G.machine H.machine leftSeed leftTime rightSeed rightTime n other chosen true padding
        (by simp [other]) length]
      simp [sourceValue, run, RunState.acceptedWord, Outcome.acceptedWord]

omit [Fintype α] in
/-- A full source block produces some output exactly on a nonempty member. -/
theorem sourceValue_full (G : UniformGenerators α) (seed time : PolynomialBound)
    (bounded : G.RunsInTime seed time) (n : ℕ) (bits : BitString)
    (length : bits.length = seed n) (nonempty : (G.layer n).Nonempty) :
    ∃ word, sourceValue G.machine time n bits = some word := by
  obtain ⟨word, produced⟩ := ((bounded n).2 bits length).mpr nonempty
  exact ⟨word, (sourceValue_eq_some_iff G.machine time n bits word).mpr
    (G.machine.produces_at_bound _ bits _ word ((bounded n).1 bits length.le) produced)⟩

theorem value_productive (G H : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (leftBound : G.toUniformGenerators.RunsInTime leftSeed leftTime)
    (rightBound : H.toUniformGenerators.RunsInTime rightSeed rightTime)
    (n : ℕ) (bits : BitString) (length : bits.length = unionSeed leftSeed rightSeed n)
    (nonempty : (lengthSlice (G.toUniformGenerators.language ∪ H.toUniformGenerators.language) n).Nonempty) :
    ∃ word, value G.machine H.machine leftSeed leftTime rightSeed rightTime n bits = some word := by
  have size : leftSeed n + rightSeed n + 1 ≤ bits.length := by
    rw [length]; exact unionSeed_lower leftSeed rightSeed n
  have leftLength : (bits.take (leftSeed n)).length = leftSeed n := by simp; omega
  have rightLength : ((bits.drop (leftSeed n)).take (rightSeed n)).length = rightSeed n := by simp; omega
  obtain ⟨word, member⟩ := nonempty
  have leftLayer : word ∈ G.toUniformGenerators.language → (G.toUniformGenerators.layer n).Nonempty := by
    intro yes; exact ⟨word, by rw [G.layer_eq_lengthSlice]; exact ⟨yes, member.2⟩⟩
  have rightLayer : word ∈ H.toUniformGenerators.language → (H.toUniformGenerators.layer n).Nonempty := by
    intro yes; exact ⟨word, by rw [H.layer_eq_lengthSlice]; exact ⟨yes, member.2⟩⟩
  rcases member.1 with left | right
  · obtain ⟨out, output⟩ := sourceValue_full G.toUniformGenerators leftSeed leftTime leftBound n _ leftLength (leftLayer left)
    unfold value
    rw [output]
    split
    · cases sourceValue H.machine rightTime n ((bits.drop (leftSeed n)).take (rightSeed n)) <;> simp
    · simp
  · obtain ⟨out, output⟩ := sourceValue_full H.toUniformGenerators rightSeed rightTime rightBound n _ rightLength (rightLayer right)
    unfold value
    rw [output]
    split
    · simp
    · cases sourceValue G.machine leftTime n (bits.take (leftSeed n)) <;> simp

end
end ComplexityOfGenerators.Simulation.UnionGenerator
