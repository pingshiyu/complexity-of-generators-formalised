import ComplexityOfGenerators.Proofs.PolynomialConcatenationSupport
import ComplexityOfGenerators.Foundations.FiniteChoiceScan

namespace ComplexityOfGenerators.Simulation.ConcatenationGenerator

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {α : Type} [Fintype α] (G H : Machine Unit Bool α)

/-- Non-replacing blocks preserve an already selected answer. -/
theorem next_traces (leftSeed leftTime rightSeed rightTime : PolynomialBound) (n : ℕ) :
    FiniteChoiceScan.TraceSpec
      (fun j => next G H leftSeed leftTime rightSeed rightTime n j)
      (blockSize leftSeed rightSeed n) := by
  intro j previous
  let left := List.replicate (leftSeed j) false
  let right := List.replicate (rightSeed (n-j)) false
  let chosen := offer previous (pairValue (UnionGenerator.sourceValue G leftTime j left)
    (UnionGenerator.sourceValue H rightTime (n-j) right)) false
  refine ⟨left ++ right ++ [false], chosen, by simp [blockSize, left, right], ?_, ?_⟩
  · intro word equal
    simp [chosen, offer, equal]
  · intro tail
    simpa only [List.append_assoc] using next_blocks G H leftSeed leftTime rightSeed rightTime n j
      previous left right false tail (by simp [left]) (by simp [right])

/-- Fixed-consumption traces, shared with the star construction. -/
theorem fold_trace (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (splits : List ℕ) (previous : Option (List α)) :
    ∃ block : BitString, ∃ answer : Option (List α),
      block.length = blocksSize leftSeed rightSeed n splits ∧
      (∀ word, previous = some word → answer = some word) ∧
      ∀ tail, splits.foldl (fun p j => next G H leftSeed leftTime rightSeed rightTime n j p)
        (previous, block ++ tail) = (answer, tail) :=
  FiniteChoiceScan.fold_trace _ _ (next_traces G H leftSeed leftTime rightSeed rightTime n) splits previous

/-- Once selected, an answer can be retained through every later split. -/
theorem fold_keep (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (n : ℕ) (splits : List ℕ) (word : List α) :
    ∃ block : BitString, block.length = blocksSize leftSeed rightSeed n splits ∧
      ∀ tail, splits.foldl (fun p j => next G H leftSeed leftTime rightSeed rightTime n j p)
        (some word, block ++ tail) = (some word, tail) :=
  FiniteChoiceScan.fold_keep _ _ (next_traces G H leftSeed leftTime rightSeed rightTime n) splits word

variable (GF HF : GeneratorFamily α) (leftSeed leftTime rightSeed rightTime : PolynomialBound)
    (leftBound : GF.toUniformGenerators.RunsInTime leftSeed leftTime)
    (rightBound : HF.toUniformGenerators.RunsInTime rightSeed rightTime)

include leftBound rightBound

/-- Every feasible pair has a source-seed/selector block forcing that pair,
regardless of the result saved by previous splits. -/
theorem next_choose (n j : ℕ) (u v : List α)
    (left : u ∈ GF.toUniformGenerators.layer j) (right : v ∈ HF.toUniformGenerators.layer (n - j)) :
    ∃ block : BitString, block.length = blockSize leftSeed rightSeed n j ∧
      ∀ previous tail,
        next GF.machine HF.machine leftSeed leftTime rightSeed rightTime n j (previous, block ++ tail) =
          (some (u ++ v), tail) := by
  obtain ⟨leftBits, leftLength, leftRun⟩ := (GF.machine.generatedLanguage_iff_budget_seed _ _ _
    (leftSeed.positive j) (leftBound j) u).mp left
  obtain ⟨rightBits, rightLength, rightRun⟩ := (HF.machine.generatedLanguage_iff_budget_seed _ _ _
    (rightSeed.positive (n - j)) (rightBound (n - j)) v).mp right
  refine ⟨leftBits ++ rightBits ++ [true], by simp [blockSize, leftLength, rightLength, Nat.add_assoc], ?_⟩
  intro previous tail
  have step := next_blocks GF.machine HF.machine leftSeed leftTime rightSeed rightTime n j previous
    leftBits rightBits true tail leftLength rightLength
  cases previous <;> simpa [UnionGenerator.sourceValue, leftRun, rightRun, RunState.acceptedWord,
    Outcome.acceptedWord, pairValue, offer] using step

/-- Any feasible split in the finite search has a full-support forcing trace. -/
theorem fold_choose (n j : ℕ) (splits : List ℕ) (occurs : j ∈ splits) (u v : List α)
    (left : u ∈ GF.toUniformGenerators.layer j) (right : v ∈ HF.toUniformGenerators.layer (n - j)) :
    ∃ block : BitString, block.length = blocksSize leftSeed rightSeed n splits ∧
      ∀ tail, splits.foldl (fun p j => next GF.machine HF.machine leftSeed leftTime rightSeed rightTime n j p)
        (none, block ++ tail) = (some (u ++ v), tail) := by
  exact FiniteChoiceScan.fold_choose _ _
    (next_traces GF.machine HF.machine leftSeed leftTime rightSeed rightTime n) splits j occurs (u ++ v)
    (next_choose GF HF leftSeed leftTime rightSeed rightTime leftBound rightBound n j u v left right)

theorem algorithm_complete (n : ℕ) (word : List α)
    (member : word ∈ lengthSlice
      (IndexedSupport.concat GF.toUniformGenerators.language HF.toUniformGenerators.language) n) :
    ∃ bits, bits.length = concatSeed leftSeed rightSeed n ∧
      algorithm GF.machine HF.machine leftSeed leftTime rightSeed rightTime n bits = some word := by
  obtain ⟨⟨u, left, v, right, rfl⟩, length⟩ := member
  have size : u.length + v.length = n := by simpa using length
  have leftLayer : u ∈ GF.toUniformGenerators.layer u.length := by
    rw [GF.layer_eq_lengthSlice]
    exact ⟨left, rfl⟩
  have rightLayer : v ∈ HF.toUniformGenerators.layer (n - u.length) := by
    rw [HF.layer_eq_lengthSlice]
    exact ⟨right, by omega⟩
  obtain ⟨block, blockLength, run⟩ := fold_choose GF HF leftSeed leftTime rightSeed rightTime leftBound rightBound
    n u.length (List.range (n + 1)) (by apply List.mem_range.mpr; omega) u v leftLayer rightLayer
  have limit : block.length ≤ concatSeed leftSeed rightSeed n :=
    blockLength.trans_le (totalBlocks_le leftSeed rightSeed n)
  let tail := List.replicate (concatSeed leftSeed rightSeed n - block.length) false
  refine ⟨block ++ tail, by simp [tail]; omega, ?_⟩
  exact congrArg Prod.fst (run tail)

end
end ComplexityOfGenerators.Simulation.ConcatenationGenerator
