import ComplexityOfGenerators.Simulation.ExactRecursive.SearchLoopBounds
import ComplexityOfGenerators.Simulation.ExactRecursive.Search

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

theorem searchSetup_bound (count : PolynomialBound) (s : Store B V) (n cap : ℕ)
    (sizes : StoreBound s cap) (index : (s 13).length = n)
    (base : n + 1 ≤ cap) (countBound : count n ≤ cap) :
    StoreBound ((searchSetup B V count).eval s) cap ∧
      (searchSetup B V count).cost s ≤ 40 * cap + 20 + Command.counterBudget count n := by
  let a := Function.update (Function.update s 12 []) 25 []
  have aSize : StoreBound a cap := (sizes.clear 12).clear 25
  obtain ⟨bSize, bCost⟩ := flag_bound B V 26 false a cap aSize (by omega)
  obtain ⟨cSize, cCost⟩ := flag_bound B V 27 false ((flag B V 26 false).eval a) cap bSize (by omega)
  let c := (flag B V 27 false).eval ((flag B V 26 false).eval a)
  have cIndex : (c 13).length = n := by simp [c, a, flag_eval, index]
  obtain ⟨lastSize, lastCost⟩ := counter_bound B V 23 (by decide) count c n cap cSize cIndex base countBound
  refine ⟨lastSize, ?_⟩
  have h12 := sizes 12
  have h25 := sizes 25
  change 3 * (s 12).length + 1 + (3 * (Function.update s 12 [] 25).length + 1 +
    ((flag B V 26 false).cost a + 1 + ((flag B V 27 false).cost ((flag B V 26 false).eval a) + 1 +
      (counter B V 23 (by decide) count).cost c))) ≤ _
  simp only [Function.update_of_ne (by decide : (25 : Fin 35) ≠ 12)]
  omega

theorem searchFinish_bound (s : Store B V) (cap words : ℕ) (sizes : StoreBound s cap)
    (positive : 1 ≤ cap) (current : (s 11).length ≤ words) (candidate : (s 25).length ≤ words) :
    StoreBound ((searchFinish B V).eval s) cap ∧
      ((searchFinish B V).eval s 11).length ≤ words ∧
      (searchFinish B V).cost s ≤ 20 * cap + 6 := by
  simp only [searchFinish, WordStack.Routine.branch]
  split
  · refine ⟨sizes.assign 25 11 33 (by decide) (by decide) (by decide) id, ?_, ?_⟩
    · simpa [WordStack.Routine.assign_eval] using candidate
    · have h11 := sizes 11
      have h25 := sizes 25
      have h33 := sizes 33
      simp only [WordStack.Routine.assign_cost]
      omega
  · dsimp only
    split
    · obtain ⟨size, cost⟩ := flag_bound B V 28 true s cap sizes positive
      exact ⟨size, by simpa [flag_eval] using current, by omega⟩
    · obtain ⟨size, cost⟩ := flag_bound B V 29 false s cap sizes positive
      exact ⟨size, by simpa [flag_eval] using current, by omega⟩

noncomputable def searchBudget (count seed time : PolynomialBound) (n cap : ℕ) : ℕ :=
  70 * cap + 40 + Command.counterBudget count n + count n * (searchStepBudget B V seed time n cap + 4)

theorem search_bound (first : α) (count seed time : PolynomialBound) (n : ℕ)
    (state : Walker α) (bits : BitString) (s : Store B V) (stored : WalkStored B V n state bits s)
    (cap words : ℕ) (sizes : StoreBound s cap) (base : n + 1 ≤ cap)
    (countBound : count n ≤ cap) (seedBound : seed n ≤ cap) (timeBound : time n + 1 ≤ cap)
    (outputBound : time n + 1 ≤ words) (current : state.word.length ≤ words)
    (space : 1 + state.word.length + count n + n + seed n + 3 * (time n + 1) ≤ cap)
    (enough : count n * (seed n + 1) ≤ bits.length) :
    StoreBound ((search B V first count seed time).eval s) cap ∧
      ((search B V first count seed time).eval s 11).length ≤ words ∧
      (search B V first count seed time).cost s ≤ searchBudget B V count seed time n cap := by
  let setup := (searchSetup B V count).eval s
  let code := WordStack.Routine.counted 23 (searchStep B V first seed time)
  let middle := code.eval^[count n] setup
  have start := searchSetup_view B V count n state.word bits s stored.input stored.index stored.random stored.empty
  have count_eq : (setup 23).length = count n := searchSetup_count B V count n s stored.index
  obtain ⟨setupSize, setupCost⟩ := searchSetup_bound B V count s n cap sizes stored.index base countBound
  obtain ⟨loopSize, loopCandidate, loopCost⟩ := searchIter_bound B V first seed time n (count n)
    state.word [] bits ⟨none, false⟩ setup start cap words (count n) setupSize base seedBound timeBound
    outputBound (by simp [setup, searchSetup, WordStack.Routine.seq, WordStack.Routine.clear, flag_eval,
      counter, CounterRoutine.routine_eval]) countBound
    (by intro i hi; exact (Shortlex.iterate_length first i).trans hi) space enough
  have middleView := searchIter_correct B V first seed time n (count n) state.word [] bits ⟨none, false⟩
    setup start enough
  have middleWord : (middle 11).length ≤ words := by
    rw [show middle 11 = letters B V state.word from middleView.input]
    simpa [letters] using current
  obtain ⟨finishSize, finishWord, finishCost⟩ := searchFinish_bound B V middle cap words loopSize (by omega)
    middleWord loopCandidate
  have eval_eq : (search B V first count seed time).eval s = (searchFinish B V).eval middle := by
    change (searchFinish B V).eval (code.eval^[(setup 23).length] setup) = _
    rw [count_eq]
  refine ⟨eval_eq ▸ finishSize, ?_, ?_⟩
  · rw [eval_eq]
    exact finishWord
  · change (searchSetup B V count).cost s + 1 +
      (WordStack.Routine.loopCost code.cost code.eval (setup 23).length setup + 1 +
        (searchFinish B V).cost (code.eval^[(setup 23).length] setup)) ≤ _
    rw [count_eq]
    change _ ≤ searchBudget B V count seed time n cap
    dsimp only [searchBudget, code, middle] at loopCost finishCost ⊢
    omega

end ComplexityOfGenerators.Simulation.ExactRecursive
