import ComplexityOfGenerators.Simulation.ExactRecursive.WalkStep

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem walkIter_correct (first : α) (count seed time : PolynomialBound) (n fuel : ℕ)
    (p : Walker α × BitString) (s : Store B V)
    (stored : WalkStored B V n p.1 p.2 s)
    (enough : fuel * (1 + count n * (seed n + 1)) ≤ p.2.length) :
    WalkStored B V n ((walkNext V first count seed time n)^[fuel] p).1
      ((walkNext V first count seed time n)^[fuel] p).2
      ((WordStack.Routine.counted 22 (walkStep B V first count seed time)).eval^[fuel] s) := by
  induction fuel generalizing p s with
  | zero => exact stored
  | succ fuel ih =>
    have firstEnough : 1 + count n * (seed n + 1) ≤ p.2.length := by
      rw [Nat.succ_mul] at enough
      omega
    have step := walkStep_correct B V first count seed time n p.1 p.2 _ stored.counter_pop firstEnough
    have restEnough : fuel * (1 + count n * (seed n + 1)) ≤
        (walkNext V first count seed time n p).2.length := by
      have length := walkNext_length V first count seed time n p
      rw [Nat.succ_mul] at enough
      omega
    exact ih _ _ step restEnough

noncomputable def walkResult (first : α) (count seed time : PolynomialBound) (n : ℕ) :
    ℕ → List α → BitString → Option (List α)
  | 0, word, _ => if word.length = n then some word else none
  | fuel + 1, word, bits =>
    if word.length = n ∧ bits.head? = some true then some word
    else match searchValue V first count seed time n word ((bits.drop 1).take (count n * (seed n + 1))) with
      | none => if word.length = n then some word else none
      | some next => walkResult first count seed time n fuel next (bits.drop (1 + count n * (seed n + 1)))

theorem walkIter_frozen (first : α) (count seed time : PolynomialBound) (n fuel : ℕ)
    (p : Walker α × BitString) (frozen : p.1.valid = false ∨ p.1.stopped = true) :
    (walkNext V first count seed time n)^[fuel] p = p := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => rw [Function.iterate_succ_apply', ih]; simp [walkNext, frozen]

theorem walkIter_answer (first : α) (count seed time : PolynomialBound) (n fuel : ℕ)
    (state : Walker α) (bits : BitString)
    (enough : fuel * (1 + count n * (seed n + 1)) ≤ bits.length) :
    (((walkNext V first count seed time n)^[fuel] (state, bits)).1).answer n =
      if state.valid = true ∧ state.stopped = false then
        walkResult V first count seed time n fuel state.word bits else state.answer n := by
  by_cases live : state.valid = true ∧ state.stopped = false
  · rw [if_pos live]
    induction fuel generalizing state bits with
    | zero => simp [Walker.answer, live.1, walkResult]
    | succ fuel ih =>
      have tailEnough : count n * (seed n + 1) ≤ (bits.drop 1).length := by
        simp only [List.length_drop]
        rw [Nat.succ_mul] at enough
        omega
      have restEnough : fuel * (1 + count n * (seed n + 1)) ≤
          (bits.drop (1 + count n * (seed n + 1))).length := by
        simp only [List.length_drop]
        rw [Nat.succ_mul] at enough
        omega
      rw [Function.iterate_succ_apply, walkResult]
      by_cases stop : state.word.length = n ∧ bits.head? = some true
      · rw [if_pos stop]
        simp only [walkNext, live.1, live.2, Bool.false_eq_true, Bool.true_eq_false, or_self, ↓reduceIte,
          stop, and_self]
        rw [walkIter_frozen V first count seed time n fuel _ (Or.inr rfl)]
        simp [Walker.answer, live.1, stop.1]
      · rw [if_neg stop]
        rw [walkNext]
        simp only [live.1, live.2, Bool.false_eq_true, Bool.true_eq_false, or_self, ↓reduceIte,
          stop]
        rw [searchValue_take V first count seed time n state.word (bits.drop 1) tailEnough]
        cases result : searchValue V first count seed time n state.word
            ((bits.drop 1).take (count n * (seed n + 1))) with
        | none =>
          by_cases equal : state.word.length = n
          · simp only [Walker.afterSearch, equal, ↓reduceIte]
            rw [walkIter_frozen V first count seed time n fuel _ (Or.inr rfl)]
            simp [Walker.answer, live.1, equal]
          · simp only [Walker.afterSearch, equal, ↓reduceIte]
            rw [walkIter_frozen V first count seed time n fuel _ (Or.inl rfl)]
            simp [Walker.answer]
        | some word =>
          exact ih {state with word := word} _ restEnough live
  · rw [if_neg live]
    have frozen : state.valid = false ∨ state.stopped = true := by
      cases hv : state.valid <;> cases hs : state.stopped <;> simp_all
    rw [walkIter_frozen V first count seed time n fuel _ frozen]

end ComplexityOfGenerators.Simulation.ExactRecursive
