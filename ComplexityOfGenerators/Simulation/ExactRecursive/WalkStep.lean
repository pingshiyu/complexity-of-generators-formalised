import ComplexityOfGenerators.Simulation.ExactRecursive.Search

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

noncomputable def walkNext (first : α) (count seed time : PolynomialBound) (n : ℕ)
    (p : Walker α × BitString) : Walker α × BitString :=
  if p.1.valid = false ∨ p.1.stopped = true then p
  else if p.1.word.length = n ∧ p.2.head? = some true then
    ({p.1 with stopped := true}, p.2.drop 1)
  else (p.1.afterSearch n (searchValue V first count seed time n p.1.word (p.2.drop 1)),
    p.2.drop (1 + count n * (seed n + 1)))

theorem walkNext_length (first : α) (count seed time : PolynomialBound) (n : ℕ)
    (p : Walker α × BitString) :
    p.2.length - (1 + count n * (seed n + 1)) ≤
      (walkNext V first count seed time n p).2.length := by
  unfold walkNext
  split
  · omega
  · split <;> simp only [List.length_drop] <;> omega

namespace WalkStored

variable {B V} {n : ℕ} {state : Walker α} {bits : BitString} {s : Store B V}

theorem stop (h : WalkStored B V n state bits s) :
    WalkStored B V n {state with stopped := true} bits ((flag B V 28 true).eval s) := by
  rcases h with ⟨hi, hn, hr, he, hv, hs⟩
  constructor <;> simp_all [flag_eval, flagWord]

end WalkStored

/-- One bounded controller step implements either the optional stop or the
complete inverse search. Frozen states preserve the remaining random block. -/
theorem walkStep_correct (first : α) (count seed time : PolynomialBound) (n : ℕ)
    (state : Walker α) (bits : BitString) (s : Store B V)
    (stored : WalkStored B V n state bits s)
    (enough : 1 + count n * (seed n + 1) ≤ bits.length) :
    WalkStored B V n (walkNext V first count seed time n (state, bits)).1
      (walkNext V first count seed time n (state, bits)).2
      ((walkStep B V first count seed time).eval s) := by
  by_cases valid : state.valid = true
  · by_cases stopped : state.stopped = true
    · simpa [walkStep, WordStack.Routine.branch, stored.valid, stored.stopped,
        valid, stopped, flagWord, WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, walkNext] using stored
    · have live : state.stopped = false := Bool.eq_false_iff.mpr stopped
      obtain ⟨tested, target⟩ := stored.length_test
      cases bits with
      | nil => simp at enough
      | cons bit rest =>
        have popped := tested.replace_random rest
        have searched :=  search_correct B V first count seed time n state rest _ popped
          (by simpa using target) (by simp only [List.length_cons] at enough; omega)
        have stop := popped.stop
        have read := coin_eval B V (search B V first count seed time) (stopOffer B V first count seed time)
          ((lengthTest B V).eval s) bit rest tested.random
        have step_eq : (walkStep B V first count seed time).eval s =
            (if bit then stopOffer B V first count seed time else search B V first count seed time).eval
              (Function.update ((lengthTest B V).eval s) 17 (rest.map Symbol.bit)) := by
          simp [walkStep, WordStack.Routine.branch, stored.valid, stored.stopped, valid, live,
            flagWord, WordStack.Routine.seq, read]
        rw [step_eq]
        cases bit with
        | false =>
          simpa [walkNext, valid, live, Nat.add_comm 1 (count n * (seed n + 1))] using searched
        | true =>
          by_cases equal : state.word.length = n
          · simpa [walkNext, valid, live, equal, stopOffer, WordStack.Routine.branch,
              target, flagWord] using stop
          · simpa [walkNext, valid, live, equal, stopOffer, WordStack.Routine.branch,
              target, flagWord, Nat.add_comm 1 (count n * (seed n + 1))] using searched
  · have invalid : state.valid = false := Bool.eq_false_iff.mpr valid
    simpa [walkStep, WordStack.Routine.branch, stored.valid, invalid, flagWord,
      WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, walkNext] using stored

end ComplexityOfGenerators.Simulation.ExactRecursive
