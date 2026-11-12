import ComplexityOfGenerators.Proofs.PolynomialStarWitnesses
import ComplexityOfGenerators.Proofs.PolynomialConcatenationProductivity

namespace ComplexityOfGenerators.Simulation.StarGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

omit [Fintype α] in
theorem next_random_length (G : Machine Unit Bool α) (seed time : PolynomialBound)
    (table : Table α) (m j : ℕ) (p : Option (List α) × BitString) :
    (next G seed time table m j p).2.length = p.2.length - (seed j + 1) := by
  simp [next, Nat.sub_sub]

omit [Fintype α] in
theorem fold_random_length (G : Machine Unit Bool α) (seed time : PolynomialBound)
    (table : Table α) (m : ℕ) (splits : List ℕ) (p : Option (List α) × BitString) :
    (splits.foldl (fun p j => next G seed time table m j p) p).2.length =
      p.2.length - FiniteChoiceScan.cost (fun j => seed j + 1) splits := by
  induction splits generalizing p with
  | nil => simp [FiniteChoiceScan.cost]
  | cons j rest ih =>
    rw [List.foldl_cons, ih, next_random_length]
    simp [FiniteChoiceScan.cost, Nat.sub_sub]

theorem tableRun_random_length (G : Machine Unit Bool α) (seed time : PolynomialBound)
    (n : ℕ) (bits : BitString) :
    (tableRun G seed time n bits).2.length = bits.length - runCost seed n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [tableRun_succ]
    change (stage G seed time _ _ _).2.length = _
    unfold stage
    rw [fold_random_length, ih, runCost_succ]
    exact Nat.sub_sub _ _ _

variable (F : GeneratorFamily α) (seed time : PolynomialBound)
    (bounded : F.toUniformGenerators.RunsInTime seed time)

include bounded in
theorem next_productive (table : Table α) (m j : ℕ) (p : Option (List α) × BitString)
    (full : seed j + 1 ≤ p.2.length)
    (available : (∃ word, p.1 = some word) ∨
      (F.toUniformGenerators.layer j).Nonempty ∧ ∃ word, table[m-j]?.bind id = some word) :
    ∃ word, (next F.machine seed time table m j p).1 = some word := by
  apply ConcatenationGenerator.offer_productive
  rcases available with old | ⟨source, v, previous⟩
  · exact Or.inl old
  · obtain ⟨u, output⟩ := UnionGenerator.sourceValue_full F.toUniformGenerators seed time bounded j
      (p.2.take (seed j)) (by simp only [List.length_take]; omega) source
    exact Or.inr ⟨u ++ v, by rw [previous]; simp [ConcatenationGenerator.pairValue, output]⟩

include bounded in
theorem fold_productive (table : Table α) (m : ℕ) (splits : List ℕ)
    (p : Option (List α) × BitString)
    (full : FiniteChoiceScan.cost (fun j => seed j + 1) splits ≤ p.2.length)
    (available : (∃ word, p.1 = some word) ∨ ∃ j ∈ splits,
      (F.toUniformGenerators.layer j).Nonempty ∧ ∃ word, table[m-j]?.bind id = some word) :
    ∃ word, (splits.foldl (fun p j => next F.machine seed time table m j p) p).1 = some word := by
  induction splits generalizing p with
  | nil => simpa using available
  | cons j rest ih =>
    have costs : seed j + 1 + FiniteChoiceScan.cost (fun j => seed j + 1) rest ≤ p.2.length := by
      simpa only [FiniteChoiceScan.cost, List.map_cons, List.sum_cons] using full
    let q := next F.machine seed time table m j p
    have remainder : FiniteChoiceScan.cost (fun j => seed j + 1) rest ≤ q.2.length := by
      dsimp only [q]
      rw [next_random_length]
      omega
    apply ih q remainder
    rcases available with old | ⟨k, occurs, viable⟩
    · exact Or.inl (next_productive F seed time bounded table m j p (by omega) (Or.inl old))
    · rcases List.mem_cons.mp occurs with equal | occurs
      · subst k
        exact Or.inl (next_productive F seed time bounded table m j p (by omega) (Or.inr viable))
      · exact Or.inr ⟨k, occurs, viable⟩

def Productive (F : GeneratorFamily α) (table : Table α) : Prop :=
  ∀ i < table.length, (lengthSlice (IndexedSupport.star F.toUniformGenerators.language) i).Nonempty →
    ∃ word, table[i]?.bind id = some word

include bounded in
theorem tableRun_productive (n : ℕ) (bits : BitString) (full : runCost seed n ≤ bits.length) :
    Productive F (tableRun F.machine seed time n bits).1 := by
  induction n with
  | zero =>
    intro i index _
    have : i = 0 := by change i < 1 at index; omega
    subst i
    exact ⟨[], rfl⟩
  | succ n ih =>
    have oldFull : runCost seed n ≤ bits.length := by rw [runCost_succ] at full; omega
    have old := ih oldFull
    let p := tableRun F.machine seed time n bits
    have tableLength : p.1.length = n+1 := tableRun_length F.machine seed time n bits
    have nextFull : stageCost seed (n+1) ≤ p.2.length := by
      dsimp only [p]
      rw [tableRun_random_length]
      rw [runCost_succ] at full
      omega
    rw [tableRun_succ]
    intro i index nonempty
    change ∃ word, (p.1 ++ [(stage F.machine seed time p.1 (n+1) p.2).1])[i]?.bind id = some word
    by_cases existing : i < p.1.length
    · rw [List.getElem?_append_left existing]
      exact old i existing nonempty
    · have equal : i = n+1 := by
        change i < (p.1 ++ [_]).length at index
        simp only [List.length_append, List.length_singleton, tableLength] at index
        omega
      subst i
      rw [List.getElem?_append_right (by omega), tableLength, Nat.sub_self]
      change ∃ word, (stage F.machine seed time p.1 (n+1) p.2).1 = some word
      obtain ⟨word, member⟩ := nonempty
      obtain ⟨j, positive, jBound, u, source, v, suffix, _⟩ :=
        IndexedSupport.star_slice_decompose _ (by omega : 0 < n+1) member
      have sourceLayer : u ∈ F.toUniformGenerators.layer j := by
        rw [F.layer_eq_lengthSlice]
        exact source
      have previous := old (n+1-j) (by rw [tableRun_length]; omega) ⟨v, suffix⟩
      apply fold_productive F seed time bounded p.1 (n+1) (List.range' 1 (n+1)) (none, p.2) nextFull
      exact Or.inr ⟨j, List.mem_range'.mpr ⟨j-1, by omega, by omega⟩, ⟨u, sourceLayer⟩, previous⟩

include bounded in
theorem algorithm_productive (n : ℕ) (bits : BitString) (length : bits.length = starSeed seed n)
    (nonempty : (lengthSlice (IndexedSupport.star F.toUniformGenerators.language) n).Nonempty) :
    ∃ word, algorithm F.machine seed time n bits = some word := by
  have full : runCost seed n ≤ bits.length := by rw [length]; exact runCost_le seed n
  obtain ⟨word, entry⟩ := tableRun_productive F seed time bounded n bits full n
    (by rw [tableRun_length]; omega) nonempty
  exact ⟨word, by simpa only [algorithm, List.getLast?_eq_getElem?, tableRun_length, Nat.add_sub_cancel] using entry⟩

end
end ComplexityOfGenerators.Simulation.StarGenerator
