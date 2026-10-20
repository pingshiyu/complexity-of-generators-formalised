import ComplexityOfGenerators.Simulation.ExactRecursive.SearchBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.WalkStep

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

noncomputable def walkStepBudget (count seed time : PolynomialBound) (n cap : ℕ) : ℕ :=
  100 * (cap + 1) + searchBudget B V count seed time n cap

theorem walkStep_bound (first : α) (count seed time : PolynomialBound) (n : ℕ)
    (state : Walker α) (bits : BitString) (s : Store B V) (stored : WalkStored B V n state bits s)
    (cap words : ℕ) (sizes : StoreBound s cap) (base : n + 1 ≤ cap)
    (countBound : count n ≤ cap) (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap)
    (outputBound : time n + 1 ≤ words) (current : state.word.length ≤ words)
    (space : 1 + words + count n + n + seed n + 3 * (time n + 1) ≤ cap)
    (enough : 1 + count n * (seed n + 1) ≤ bits.length) :
    StoreBound ((walkStep B V first count seed time).eval s) cap ∧
      ((walkStep B V first count seed time).eval s 11).length ≤ words ∧
      (walkStep B V first count seed time).cost s ≤ walkStepBudget B V count seed time n cap := by
  have wordSize : (s 11).length ≤ words := by simpa [stored.input, letters] using current
  by_cases valid : state.valid = true
  · by_cases stopped : state.stopped = true
    · simpa [walkStep, WordStack.Routine.branch, stored.valid, stored.stopped, valid, stopped, flagWord,
        WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, Local.ticks, walkStepBudget] using
        And.intro sizes (And.intro wordSize (by omega : 2 ≤ 100 * (cap + 1) + searchBudget B V count seed time n cap))
    · have live : state.stopped = false := Bool.eq_false_iff.mpr stopped
      obtain ⟨tested, target⟩ := stored.length_test
      let t := (lengthTest B V).eval s
      change WalkStored B V n state bits t at tested
      have testedSize : StoreBound t cap := sizes.lengthTest lengthSlots .unit (by omega)
      have testedCost := LengthTest.routine_cost (O := α) lengthSlots (Symbol.unit : Cell B V) s cap sizes
      have testedWord : (t 11).length ≤ words := by simpa [tested.input, letters] using current
      cases bits with
      | nil => simp at enough
      | cons bit rest =>
        let popped := Function.update t 17 (rest.map Symbol.bit)
        have popSize : StoreBound popped cap := testedSize.update 17 _ (by
          have bound := testedSize 17
          rw [tested.random] at bound
          simp only [List.length_map, List.length_cons] at bound ⊢
          omega)
        have popView := tested.replace_random rest
        obtain ⟨searchSize, searchWord, searchCost⟩ := search_bound B V first count seed time n state rest popped
          popView cap words popSize base countBound seedBound timeBound outputBound current (by omega)
          (by simp only [List.length_cons] at enough; omega)
        obtain ⟨stopSize, stopCost⟩ := flag_bound B V 28 true popped cap popSize (by omega)
        have stopWord : ((flag B V 28 true).eval popped 11).length ≤ words := by
          simpa [flag_eval, popped] using testedWord
        have head : (t 17).head? = some (.bit bit) := by rw [tested.random]; rfl
        have pop : (Local.pop (17 : Fin 35)).eval t = popped := by simp [Local.eval_pop, tested.random, popped]
        have coinCost : (coin B V (search B V first count seed time) (stopOffer B V first count seed time)).cost t =
            3 + (if bit then stopOffer B V first count seed time else search B V first count seed time).cost popped := by
          simp only [coin, WordStack.Routine.branch, head, WordStack.Routine.seq, WordStack.Routine.ofLocal]
          rw [pop]
          cases bit <;> simp [Local.pop, Local.ticks] <;> omega
        have stepCost : (walkStep B V first count seed time).cost s =
            6 + (lengthTest B V).cost s +
              (if bit then stopOffer B V first count seed time else search B V first count seed time).cost popped := by
          simp only [walkStep, WordStack.Routine.branch, stored.valid, stored.stopped, valid, live,
            flagWord, ↓reduceIte, List.head?_cons, List.head?_nil, Option.isNone_some, Option.isSome_none,
            Bool.false_eq_true, WordStack.Routine.seq]
          change 1 + (1 + ((lengthTest B V).cost s + 1 +
            (coin B V (search B V first count seed time) (stopOffer B V first count seed time)).cost t)) = _
          rw [coinCost]
          omega
        have stepEval : (walkStep B V first count seed time).eval s =
            (if bit then stopOffer B V first count seed time else search B V first count seed time).eval popped := by
          have read := coin_eval B V (search B V first count seed time) (stopOffer B V first count seed time)
            t bit rest tested.random
          simp [walkStep, WordStack.Routine.branch, stored.valid, stored.stopped, valid, live,
            flagWord, WordStack.Routine.seq, read, t, popped]
        rw [stepEval, stepCost]
        cases bit with
        | false =>
          simp only [Bool.false_eq_true, ↓reduceIte]
          refine ⟨searchSize, searchWord, ?_⟩
          change (lengthTest B V).cost s ≤ 80 * (cap + 1) at testedCost
          dsimp only [walkStepBudget]
          omega
        | true =>
          simp only [Bool.true_eq_false, ↓reduceIte, stopOffer, WordStack.Routine.branch]
          split
          · refine ⟨stopSize, stopWord, ?_⟩
            change (lengthTest B V).cost s ≤ 80 * (cap + 1) at testedCost
            dsimp only [walkStepBudget, searchBudget]
            omega
          · refine ⟨searchSize, searchWord, ?_⟩
            change (lengthTest B V).cost s ≤ 80 * (cap + 1) at testedCost
            dsimp only [walkStepBudget]
            omega
  · have invalid : state.valid = false := Bool.eq_false_iff.mpr valid
    simpa [walkStep, WordStack.Routine.branch, stored.valid, invalid, flagWord,
      WordStack.Routine.skip, WordStack.Routine.ofLocal, Local.eval, Local.ticks, walkStepBudget] using
        And.intro sizes (And.intro wordSize (by omega : 1 ≤ 100 * (cap + 1) + searchBudget B V count seed time n cap))

end ComplexityOfGenerators.Simulation.ExactRecursive
