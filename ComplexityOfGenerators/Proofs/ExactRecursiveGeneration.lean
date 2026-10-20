import ComplexityOfGenerators.Simulation.ExactRecursive.Execution
import ComplexityOfGenerators.Simulation.ExactRecursive.TableBridge
import ComplexityOfGenerators.Proofs.EmptyWordGeneration
import ComplexityOfGenerators.Proofs.TrialBoundExamples

/-! Proposition A.23.2. A finite native generator executes the corrected
optional-stopping algorithm. Both its seed budget and its actual running time
are polynomial in the unary length index. -/

namespace ComplexityOfGenerators

open Simulation.ExactRecursive Simulation.WordStack

namespace ExactRecursiveGenerators

variable {α : Type} [Fintype α] {L : Language α} {R : SelfReduction L}

theorem mem_pg_nonempty [Nonempty α] (G : ExactRecursiveGenerators R) : L ∈ PG α := by
  classical
  obtain ⟨baseSeed, baseTime, bounded⟩ := G.baseTime
  let alphabet : List α := List.ofFn (Fintype.equivFin α).symm
  have card : alphabet.length = Fintype.card α := by simp [alphabet]
  have positive : 0 < Fintype.card α := Fintype.card_pos
  let first : α := Simulation.CyclicGenerator.alphabet.symm ⟨0, positive⟩
  have least : Simulation.CyclicGenerator.firstLetter = some first := by
    simp [Simulation.CyclicGenerator.firstLetter, positive, first]
  let E := nativeTable (R := R) alphabet card first least
  let seed := G.tableAlgorithmSeedBound baseSeed E
  let count := R.labelCountBound alphabet
  have enough (n : ℕ) : baseSeed n + R.rankBound n * (1 + count n * (G.inverseSeed n + 1)) ≤ seed n := by
    simpa [tableAlgorithmSeed, tableWalkSeed, tableSeed, E, nativeTable, LabelEnumeration.shortlex,
      count, seed] using G.tableAlgorithm_seed_polynomial baseSeed E n
  have algorithm_eq (n : ℕ) (bits : BitString) :
      Simulation.ExactRecursive.algorithm G.base.machine G.inverse first baseSeed baseTime G.inverseSeed G.inverseTime
        count R.rankBound n bits = G.tableAlgorithm baseSeed baseTime E n bits :=
    G.native_algorithm_eq alphabet card first least baseSeed baseTime n bits
  apply Command.mem_pg
    (command G.base.machine G.inverse first baseSeed baseTime G.inverseSeed G.inverseTime count R.rankBound seed) 0 L seed
    (stackTime G.base.machine G.inverse baseSeed baseTime G.inverseSeed G.inverseTime count R.rankBound seed)
    (commandValue G.base.machine G.inverse first baseSeed baseTime G.inverseSeed G.inverseTime count R.rankBound seed)
  · intro n bits
    obtain ⟨t, _, result, run, value⟩ := command_runs G.base.machine G.inverse first baseSeed baseTime G.inverseSeed
      G.inverseTime count R.rankBound seed n _ _
      (budgetConditions baseSeed baseTime G.inverseSeed G.inverseTime count R.rankBound seed n (enough n)) bits
    exact ⟨t, result, run, value⟩
  · intro n bits x output
    unfold commandValue at output
    split at output
    · rename_i full
      rw [algorithm_eq] at output
      rw [← G.polynomial_tableAlgorithm_support baseSeed baseTime bounded E n]
      exact ⟨bits.take (seed n), by simp only [List.length_take, Nat.min_eq_left full]; rfl, output⟩
    · simp at output
  · intro n x member
    rw [← G.polynomial_tableAlgorithm_support baseSeed baseTime bounded E n] at member
    obtain ⟨bits, length, output⟩ := member
    refine ⟨bits, length, ?_⟩
    change bits.length = seed n at length
    simp only [commandValue, ← length, le_refl, ite_true, List.take_length, algorithm_eq]
    exact output
  · intro n bits length nonempty
    obtain ⟨x, output⟩ := (G.polynomial_tableAlgorithm_full_trial_iff baseSeed baseTime bounded E n bits length).mpr nonempty
    refine ⟨x, ?_⟩
    simp only [commandValue, ← length, le_refl, ite_true, List.take_length, algorithm_eq]
    exact output
  · intro n bits length
    exact command_time G.base.machine G.inverse first baseSeed baseTime G.inverseSeed G.inverseTime
      count R.rankBound seed n (enough n) bits length

/-- Exact recursive generation suffices; the machine construction also works
for the degenerate empty alphabet. -/
theorem mem_pg (G : ExactRecursiveGenerators R) : L ∈ PG α := by
  classical
  cases isEmpty_or_nonempty α with
  | inl empty =>
    letI := empty
    have words (w : Word α) : w = [] := by
      cases w with
      | nil => rfl
      | cons a _ => exact isEmptyElim a
    by_cases member : [] ∈ L
    · have equal : L = {[]} := by ext w; rw [words w]; simp [member]
      rw [equal]
      exact empty_word_language_in_pg α
    · have equal : L = ∅ := by ext w; rw [words w]; simp [member]
      rw [equal]
      exact delayed_empty_language_in_pg α
  | inr nonempty =>
    letI := nonempty
    exact G.mem_pg_nonempty

end ExactRecursiveGenerators

/-- **Proposition A.23.2.** Every exactly recursively generable language is
polynomial-time generable. The verified construction allows an optional stop
at each length-`n` ancestor and otherwise follows positive inverse labels. -/
theorem exactlyRecursivelyGenerable_mem_pg {α : Type} [Fintype α] {L : Language α}
    (h : ExactlyRecursivelyGenerable L) : L ∈ PG α := by
  obtain ⟨R, _, ⟨G⟩⟩ := h
  exact G.mem_pg

end ComplexityOfGenerators
