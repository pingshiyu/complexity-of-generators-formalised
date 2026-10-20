import ComplexityOfGenerators.Simulation.ExactRecursive.WalkStepBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.WalkLoop

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem walkIter_bound (first : α) (count seed time : PolynomialBound) (n steps : ℕ)
    (p : Walker α × BitString) (s : Store B V) (stored : WalkStored B V n p.1 p.2 s)
    (cap words : ℕ) (sizes : StoreBound s cap) (base : n + 1 ≤ cap)
    (countBound : count n ≤ cap) (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap)
    (outputBound : time n + 1 ≤ words) (current : p.1.word.length ≤ words)
    (space : 1 + words + count n + n + seed n + 3 * (time n + 1) ≤ cap)
    (enough : steps * (1 + count n * (seed n + 1)) ≤ p.2.length) :
    let code := WordStack.Routine.counted 22 (walkStep B V first count seed time)
    StoreBound (code.eval^[steps] s) cap ∧
      ((code.eval^[steps] s) 11).length ≤ words ∧
      WordStack.Routine.loopCost code.cost code.eval steps s ≤
        steps * (walkStepBudget B V count seed time n cap + 4) := by
  induction steps generalizing p s with
  | zero =>
    exact ⟨sizes, by simpa [stored.input, letters] using current, by simp [WordStack.Routine.loopCost]⟩
  | succ steps ih =>
    let popped := (Local.pop (22 : Fin 35)).eval s
    have popSize : StoreBound popped cap := sizes.update 22 _ (by
      change (s 22).tail.length ≤ cap
      have := sizes 22
      simp only [List.length_tail]
      omega)
    have firstEnough : 1 + count n * (seed n + 1) ≤ p.2.length := by rw [Nat.succ_mul] at enough; omega
    have nextView := walkStep_correct B V first count seed time n p.1 p.2 popped stored.counter_pop firstEnough
    obtain ⟨nextSize, nextWord, nextCost⟩ := walkStep_bound B V first count seed time n p.1 p.2 popped
      stored.counter_pop cap words popSize base countBound seedBound timeBound outputBound current space firstEnough
    have nextCurrent : (walkNext V first count seed time n p).1.word.length ≤ words := by
      simpa [nextView.input, letters] using nextWord
    have restEnough : steps * (1 + count n * (seed n + 1)) ≤ (walkNext V first count seed time n p).2.length := by
      have length := walkNext_length V first count seed time n p
      rw [Nat.succ_mul] at enough
      omega
    obtain ⟨lastSize, lastWord, lastCost⟩ := ih _ _ nextView nextSize nextCurrent restEnough
    refine ⟨lastSize, lastWord, ?_⟩
    change (WordStack.Routine.counted 22 (walkStep B V first count seed time)).cost s + 2 +
      WordStack.Routine.loopCost _ _ steps ((walkStep B V first count seed time).eval popped) ≤ _
    have countCost : (WordStack.Routine.counted 22 (walkStep B V first count seed time)).cost s =
        2 + (walkStep B V first count seed time).cost popped := rfl
    rw [countCost, Nat.succ_mul]
    omega

end ComplexityOfGenerators.Simulation.ExactRecursive
