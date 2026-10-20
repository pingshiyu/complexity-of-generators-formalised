import ComplexityOfGenerators.Simulation.ExactRecursive.Selection
import ComplexityOfGenerators.Simulation.WordStack.StoreBounds

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem flag_bound (reg : Fin 35) (b : Bool) (s : Store B V) (cap : ℕ)
    (sizes : StoreBound s cap) (positive : 1 ≤ cap) :
    StoreBound ((flag B V reg b).eval s) cap ∧ (flag B V reg b).cost s ≤ 3 * cap + 2 := by
  constructor
  · rw [flag_eval]
    apply sizes.update
    cases b <;> simp_all [flagWord]
  · have size := sizes reg
    cases b <;> simp [flag, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.skip,
      WordStack.Routine.ofLocal, Local.push, Local.ticks] <;> omega

theorem takeOutput_bound (dst : Fin 35) (different : (10 : Fin 35) ≠ dst)
    (f : Cell B V → Cell B V) (s : Store B V) (cap : ℕ) (sizes : StoreBound s cap) :
    StoreBound ((takeOutput B V dst different f).eval s) cap ∧
      (takeOutput B V dst different f).cost s ≤ 9 * cap + 1 := by
  constructor
  · rw [takeOutput_eval]
    exact (sizes.clear 10).update dst _ (by simpa using sizes 10)
  · have source := sizes 10
    have target := sizes dst
    simp only [takeOutput, WordStack.Routine.seq, WordStack.Routine.clear, WordStack.Routine.transfer,
      Function.update_of_ne different]
    omega

theorem offer_bound (bit : Bool) (s : Store B V) (cap words : ℕ)
    (sizes : StoreBound s cap) (positive : 1 ≤ cap)
    (candidate : (s 25).length ≤ words) (output : (s 10).length ≤ words) :
    StoreBound ((offer B V bit).eval s) cap ∧
      ((offer B V bit).eval s 25).length ≤ words ∧
      (offer B V bit).cost s ≤ 20 * cap + 20 := by
  unfold offer
  simp only [WordStack.Routine.branch]
  split
  · exact ⟨sizes, candidate, by simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]⟩
  · dsimp only
    split
    · exact ⟨sizes, candidate, by simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]⟩
    · dsimp only
      split
      · obtain ⟨taken, takenCost⟩ := takeOutput_bound B V 25 (by decide) (inverseOutput B V) s cap sizes
        obtain ⟨found, foundCost⟩ := flag_bound B V 27 true _ cap taken positive
        obtain ⟨locked, lockedCost⟩ := flag_bound B V 26 true _ cap found positive
        have newCandidate : ((takeOutput B V 25 (by decide) (inverseOutput B V)).eval s 25).length ≤ words := by
          simpa [takeOutput_eval] using output
        cases bit <;>
          simp only [Bool.false_eq_true, ↓reduceIte, WordStack.Routine.seq,
            WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, Local.ticks]
        · refine ⟨found, ?_, ?_⟩
          · simpa [flag_eval] using newCandidate
          · omega
        · refine ⟨locked, ?_, ?_⟩
          · simpa [flag_eval] using newCandidate
          · omega
      · exact ⟨sizes, candidate, by simp [WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.ticks]⟩

theorem increment_bound (first : α) (s : Store B V) (label : List α) (cap : ℕ)
    (sizes : StoreBound s cap) (word : s 12 = letters B V label)
    (nextSize : (Shortlex.next first label).length ≤ cap) :
    StoreBound ((increment B V first).eval s) cap ∧
      (increment B V first).cost s ≤ 15 * cap + 7 := by
  constructor
  · intro j
    by_cases isWord : j = 12
    · subst j
      rw [increment_word B V first s label word]
      simpa [letters] using nextSize
    · by_cases scratch : j = 24
      · subst j
        simp [increment, WordCounter.routine_eval]
      · rw [increment_fixes B V first j isWord scratch]
        exact sizes j
  · have cost := WordCounter.routine_cost (O := α) 12 24 (by decide)
      (Symbol.letter first : Cell B V) (nextLetter B V) s
    have h12 := sizes 12
    have h24 := sizes 24
    exact cost.trans (by omega)

end ComplexityOfGenerators.Simulation.ExactRecursive
