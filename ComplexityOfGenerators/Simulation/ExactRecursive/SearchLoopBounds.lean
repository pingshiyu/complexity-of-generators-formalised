import ComplexityOfGenerators.Simulation.ExactRecursive.SearchStepBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.SearchLoop

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem searchIter_bound (first : α) (seed time : PolynomialBound) (n steps : ℕ)
    (y label : List α) (bits : BitString) (selection : BoundedTrialChoice.Selection (List α))
    (s : Store B V) (stored : SearchStored B V n y label bits selection s)
    (cap words labelCap : ℕ) (sizes : StoreBound s cap) (base : n + 1 ≤ cap)
    (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap) (outputBound : time n + 1 ≤ words)
    (candidate : (s 25).length ≤ words) (labelBound : labelCap ≤ cap)
    (labels : ∀ i ≤ steps, ((Shortlex.next first)^[i] label).length ≤ labelCap)
    (space : 1 + y.length + labelCap + n + seed n + 3 * (time n + 1) ≤ cap)
    (enough : steps * (seed n + 1) ≤ bits.length) :
    let code := WordStack.Routine.counted 23 (searchStep B V first seed time)
    StoreBound (code.eval^[steps] s) cap ∧
      ((code.eval^[steps] s) 25).length ≤ words ∧
      WordStack.Routine.loopCost code.cost code.eval steps s ≤
        steps * (searchStepBudget B V seed time n cap + 4) := by
  induction steps generalizing label bits selection s with
  | zero => exact ⟨sizes, candidate, by simp [WordStack.Routine.loopCost]⟩
  | succ steps ih =>
    let popped := (Local.pop (23 : Fin 35)).eval s
    have popSize : StoreBound popped cap := sizes.update 23 _ (by
      have := sizes 23
      change (s 23).tail.length ≤ cap
      simp only [List.length_tail]
      omega)
    have popCandidate : (popped 25).length ≤ words := by simpa [popped, Local.eval_pop] using candidate
    have firstEnough : seed n + 1 ≤ bits.length := by rw [Nat.succ_mul] at enough; omega
    have nextView := searchStep_correct B V first seed time n y label bits selection popped stored.counter_pop firstEnough
    obtain ⟨nextSize, nextCandidate, nextCost⟩ := searchStep_bound B V first seed time n y label bits selection
      popped stored.counter_pop cap words popSize base seedBound timeBound outputBound popCandidate
      ((by simpa using labels 1 (by omega) : (Shortlex.next first label).length ≤ labelCap).trans labelBound)
      (by have := labels 0 (by omega); simp only [Function.iterate_zero, id_eq] at this; omega)
    have nextLabels : ∀ i ≤ steps, ((Shortlex.next first)^[i] (Shortlex.next first label)).length ≤ labelCap := by
      intro i hi
      simpa only [Function.iterate_succ_apply] using labels (i + 1) (by omega)
    have restEnough : steps * (seed n + 1) ≤ (bits.drop (seed n + 1)).length := by
      simp only [List.length_drop]
      rw [Nat.succ_mul] at enough
      omega
    obtain ⟨lastSize, lastCandidate, lastCost⟩ := ih _ _ _ _ nextView nextSize nextCandidate nextLabels restEnough
    refine ⟨lastSize, lastCandidate, ?_⟩
    change (WordStack.Routine.counted 23 (searchStep B V first seed time)).cost s + 2 +
      WordStack.Routine.loopCost _ _ steps ((searchStep B V first seed time).eval popped) ≤ _
    have countCost : (WordStack.Routine.counted 23 (searchStep B V first seed time)).cost s =
        2 + (searchStep B V first seed time).cost popped := rfl
    rw [countCost, Nat.succ_mul]
    omega

end ComplexityOfGenerators.Simulation.ExactRecursive
