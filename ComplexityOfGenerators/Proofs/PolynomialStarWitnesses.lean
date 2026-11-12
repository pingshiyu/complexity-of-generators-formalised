import ComplexityOfGenerators.Proofs.PolynomialStarSupport
import ComplexityOfGenerators.Foundations.FiniteChoiceScan

namespace ComplexityOfGenerators.Simulation.StarGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α]

def stageCost (seed : PolynomialBound) (m : ℕ) : ℕ :=
  FiniteChoiceScan.cost (fun j => seed j + 1) (List.range' 1 m)

def runCost (seed : PolynomialBound) (n : ℕ) : ℕ :=
  FiniteChoiceScan.cost (stageCost seed) (List.range' 1 n)

def starSeed (seed : PolynomialBound) : PolynomialBound :=
  (⟨1, 2, by decide⟩ : PolynomialBound).mul (seed.add ⟨1, 0, by decide⟩)

@[simp] theorem runCost_zero (seed : PolynomialBound) : runCost seed 0 = 0 := rfl

theorem runCost_succ (seed : PolynomialBound) (n : ℕ) :
    runCost seed (n + 1) = runCost seed n + stageCost seed (n + 1) := by
  simp [runCost, FiniteChoiceScan.cost, List.range'_concat, List.map_append, List.sum_append,
    Nat.add_comm]

theorem cost_le {I : Type} (size : I → ℕ) (items : List I) (bound : ℕ)
    (bounded : ∀ i ∈ items, size i ≤ bound) :
    FiniteChoiceScan.cost size items ≤ items.length * bound := by
  induction items with
  | nil => simp [FiniteChoiceScan.cost]
  | cons i rest ih =>
    have head := bounded i (by simp)
    have tail := ih (by intro j member; exact bounded j (by simp [member]))
    simp only [FiniteChoiceScan.cost, List.map_cons, List.sum_cons, List.length_cons] at *
    nlinarith

theorem stageCost_le (seed : PolynomialBound) (m n : ℕ) (index : m ≤ n) :
    stageCost seed m ≤ n * (seed n + 1) := by
  have bound := cost_le (fun j => seed j + 1) (List.range' 1 m) (seed n + 1) (by
    intro j member
    obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp member
    have : 1 + k ≤ n := by simpa using (show 1 + k * 1 ≤ n by omega)
    simpa only [Nat.one_mul] using Nat.add_le_add_right (seed.monotone this) 1)
  simp only [List.length_range'] at bound
  exact bound.trans (Nat.mul_le_mul_right _ index)

theorem runCost_le (seed : PolynomialBound) (n : ℕ) : runCost seed n ≤ starSeed seed n := by
  have bound := cost_le (stageCost seed) (List.range' 1 n) (n * (seed n + 1)) (by
    intro m member
    obtain ⟨k, hk, rfl⟩ := List.mem_range'.mp member
    apply stageCost_le seed _ n
    simp only [Nat.one_mul]
    omega)
  simp only [List.length_range'] at bound
  have one : seed n + 1 ≤ (seed.add ⟨1, 0, by decide⟩) n := by
    simpa [PolynomialBound.eval] using seed.add_le ⟨1, 0, by decide⟩ n
  have polynomial : starSeed seed n = (n + 1)^2 * (seed.add ⟨1, 0, by decide⟩) n := by
    simp [starSeed, PolynomialBound.mul, PolynomialBound.eval, pow_add]
    ring
  change runCost seed n ≤ _ at bound
  calc
    runCost seed n ≤ n * (n * (seed n + 1)) := bound
    _ ≤ (n+1)^2 * (seed n + 1) := by nlinarith
    _ ≤ starSeed seed n := by rw [polynomial]; exact Nat.mul_le_mul_left _ one

theorem next_blocks (G : Machine Unit Bool α) (seed time : PolynomialBound) (table : Table α)
    (m j : ℕ) (previous : Option (List α)) (block : BitString) (coin : Bool) (tail : BitString)
    (length : block.length = seed j) :
    next G seed time table m j (previous, block ++ [coin] ++ tail) =
      (ConcatenationGenerator.offer previous
        (ConcatenationGenerator.pairValue (UnionGenerator.sourceValue G time j block)
          (table[m-j]?.bind id)) coin, tail) := by
  cases coin <;> simp [next, List.append_assoc, List.drop_append, ← length] <;> omega

theorem next_traces (G : Machine Unit Bool α) (seed time : PolynomialBound) (table : Table α) (m : ℕ) :
    FiniteChoiceScan.TraceSpec (fun j => next G seed time table m j) (fun j => seed j + 1) := by
  intro j previous
  let source := List.replicate (seed j) false
  let chosen := ConcatenationGenerator.offer previous
    (ConcatenationGenerator.pairValue (UnionGenerator.sourceValue G time j source)
      (table[m-j]?.bind id)) false
  refine ⟨source ++ [false], chosen, by simp [source], ?_, ?_⟩
  · intro word equal
    simp [chosen, ConcatenationGenerator.offer, equal]
  · intro tail
    change next G seed time table m j (previous, (source ++ [false]) ++ tail) = _
    simpa only [List.append_assoc] using next_blocks G seed time table m j previous source false tail (by simp [source])

theorem stage_trace (G : Machine Unit Bool α) (seed time : PolynomialBound) (table : Table α) (m : ℕ) :
    ∃ block : BitString, ∃ answer : Option (List α), block.length = stageCost seed m ∧
      ∀ tail, stage G seed time table m (block ++ tail) = (answer, tail) := by
  obtain ⟨block, answer, length, _, trace⟩ := FiniteChoiceScan.fold_trace _ _
    (next_traces G seed time table m) (List.range' 1 m) none
  exact ⟨block, answer, length, trace⟩

variable (F : GeneratorFamily α) (seed time : PolynomialBound)
    (bounded : F.toUniformGenerators.RunsInTime seed time)

include bounded in
theorem next_choose (table : Table α) (m j : ℕ) (u v : List α)
    (source : u ∈ F.toUniformGenerators.layer j) (previous : table[m-j]?.bind id = some v) :
    ∃ block : BitString, block.length = seed j + 1 ∧
      ∀ answer tail, next F.machine seed time table m j (answer, block ++ tail) = (some (u ++ v), tail) := by
  obtain ⟨bits, length, run⟩ := (F.machine.generatedLanguage_iff_budget_seed _ _ _
    (seed.positive j) (bounded j) u).mp source
  refine ⟨bits ++ [true], by simp [length], ?_⟩
  intro answer tail
  have trace := next_blocks F.machine seed time table m j answer bits true tail length
  rw [previous] at trace
  cases answer <;> simpa [List.append_assoc, UnionGenerator.sourceValue, run, RunState.acceptedWord,
    Outcome.acceptedWord, ConcatenationGenerator.offer, ConcatenationGenerator.pairValue] using trace

include bounded in
theorem stage_choose (table : Table α) (m j : ℕ) (positive : 1 ≤ j) (index : j ≤ m) (u v : List α)
    (source : u ∈ F.toUniformGenerators.layer j) (previous : table[m-j]?.bind id = some v) :
    ∃ block : BitString, block.length = stageCost seed m ∧
      ∀ tail, stage F.machine seed time table m (block ++ tail) = (some (u ++ v), tail) := by
  have occurs : j ∈ List.range' 1 m := List.mem_range'.mpr ⟨j-1, by omega, by omega⟩
  exact FiniteChoiceScan.fold_choose _ _ (next_traces F.machine seed time table m) _ j occurs (u ++ v)
    (next_choose F seed time bounded table m j u v source previous)

include bounded in
theorem tableRun_forces (n : ℕ) : ∀ i ≤ n, ∀ word,
    word ∈ lengthSlice (IndexedSupport.star F.toUniformGenerators.language) i →
    ∃ block : BitString, ∃ table : Table α, block.length = runCost seed n ∧
      table.length = n + 1 ∧ table[i]?.bind id = some word ∧
      ∀ tail, tableRun F.machine seed time n (block ++ tail) = (table, tail) := by
  induction n with
  | zero =>
    intro i index word member
    have zero : i = 0 := by omega
    subst i
    have empty : word = [] := List.length_eq_zero_iff.mp member.2
    subst word
    exact ⟨[], [some []], rfl, rfl, rfl, by intro tail; rfl⟩
  | succ n ih =>
    intro i index word member
    by_cases old : i ≤ n
    · obtain ⟨block, table, length, tableLength, entry, trace⟩ := ih i old word member
      obtain ⟨nextBits, answer, nextLength, nextRun⟩ := stage_trace F.machine seed time table (n+1)
      refine ⟨block ++ nextBits, table ++ [answer], ?_, by simp [tableLength], ?_, ?_⟩
      · simp only [List.length_append, length, nextLength, runCost_succ]
      · rw [List.getElem?_append_left (by omega)]
        exact entry
      · intro tail
        rw [tableRun_succ, List.append_assoc, trace]
        simp only [extend, nextRun]
    · have equal : i = n + 1 := by omega
      subst i
      obtain ⟨j, positive, jBound, u, source, v, suffix, equal⟩ :=
        IndexedSupport.star_slice_decompose _ (by omega : 0 < n+1) member
      have kBound : n+1-j ≤ n := by omega
      obtain ⟨block, table, length, tableLength, entry, trace⟩ := ih _ kBound v suffix
      have sourceLayer : u ∈ F.toUniformGenerators.layer j := by
        rw [F.layer_eq_lengthSlice]
        exact source
      obtain ⟨nextBits, nextLength, nextRun⟩ := stage_choose F seed time bounded table (n+1) j
        positive jBound u v sourceLayer entry
      refine ⟨block ++ nextBits, table ++ [some (u ++ v)], ?_, by simp [tableLength], ?_, ?_⟩
      · simp only [List.length_append, length, nextLength, runCost_succ]
      · rw [List.getElem?_append_right (by omega), tableLength, Nat.sub_self]
        simp [equal]
      · intro tail
        rw [tableRun_succ, List.append_assoc, trace]
        simp only [extend, nextRun]

include bounded in
theorem algorithm_complete (n : ℕ) (word : List α)
    (member : word ∈ lengthSlice (IndexedSupport.star F.toUniformGenerators.language) n) :
    ∃ bits, bits.length = starSeed seed n ∧ algorithm F.machine seed time n bits = some word := by
  obtain ⟨block, table, length, tableLength, entry, trace⟩ :=
    tableRun_forces F seed time bounded n n le_rfl word member
  have limit := length.trans_le (runCost_le seed n)
  let tail := List.replicate (starSeed seed n - block.length) false
  refine ⟨block ++ tail, by simp [tail]; omega, ?_⟩
  unfold algorithm
  rw [trace]
  simpa only [List.getLast?_eq_getElem?, tableLength, Nat.add_sub_cancel] using entry

end
end ComplexityOfGenerators.Simulation.StarGenerator
