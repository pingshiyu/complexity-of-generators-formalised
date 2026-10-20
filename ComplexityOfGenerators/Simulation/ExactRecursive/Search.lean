import ComplexityOfGenerators.Simulation.ExactRecursive.WalkView

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

noncomputable def searchValue (first : α) (count seed time : PolynomialBound)
    (n : ℕ) (y : List α) (bits : BitString) : Option (List α) :=
  BoundedTrialChoice.run (seed n) (entriesFrom V first time n y (count n) []) bits

theorem search_correct (first : α) (count seed time : PolynomialBound) (n : ℕ)
    (state : Walker α) (bits : BitString) (s : Store B V)
    (stored : WalkStored B V n state bits s)
    (target : s 30 = flagWord B V (decide (state.word.length = n)))
    (enough : count n * (seed n + 1) ≤ bits.length) :
    WalkStored B V n (state.afterSearch n (searchValue V first count seed time n state.word bits))
      (bits.drop (count n * (seed n + 1))) ((search B V first count seed time).eval s) := by
  let setup := (searchSetup B V count).eval s
  let loopCode := WordStack.Routine.iterate 23 (searchStep B V first seed time)
    (searchStep_fixes B V first seed time 23 (Or.inr rfl))
  let middle := loopCode.eval setup
  have initial := searchSetup_view B V count n state.word bits s stored.input stored.index stored.random stored.empty
  have iteration := searchIter_correct B V first seed time n (count n) state.word [] bits ⟨none, false⟩ setup initial enough
  have count_eq : (setup 23).length = count n := searchSetup_count B V count n s stored.index
  have represented : SearchStored B V n state.word ((Shortlex.next first)^[count n] [])
      (bits.drop (count n * (seed n + 1)))
      (BoundedTrialChoice.scan (seed n) (entriesFrom V first time n state.word (count n) []) bits ⟨none, false⟩) middle := by
    simpa only [middle, loopCode, WordStack.Routine.iterate, count_eq] using iteration
  have frame (j : Fin 35) (large : 28 ≤ j.val) : middle j = s j := by
    have notClock : j ≠ 23 := by omega
    exact ((searchSetup_fixes_high B V count j large).seq
      (WordStack.Routine.Fixes.iterate 23 (searchStep B V first seed time)
        (searchStep_fixes B V first seed time 23 (Or.inr rfl)) j notClock
        (searchStep_fixes_high B V first seed time j large))) s
  have finish := searchFinish_view B V n state _ _ _ middle represented
    ((frame 29 (by decide)).trans stored.valid) ((frame 28 (by decide)).trans stored.stopped)
    ((frame 30 (by decide)).trans target)
  simpa only [search, WordStack.Routine.seq, BoundedTrialChoice.scan_empty, searchValue] using finish

theorem searchValue_take (first : α) (count seed time : PolynomialBound) (n : ℕ) (y : List α)
    (bits : BitString) (enough : count n * (seed n + 1) ≤ bits.length) :
    searchValue V first count seed time n y bits =
      searchValue V first count seed time n y (bits.take (count n * (seed n + 1))) := by
  have length : (bits.take (count n * (seed n + 1))).length =
      BoundedTrialChoice.seedLength (seed n) (entriesFrom V first time n y (count n) []) := by
    simp [BoundedTrialChoice.seedLength, entriesFrom_eq, Nat.min_eq_left enough]
  simpa only [List.take_append_drop, searchValue] using
    BoundedTrialChoice.append_unused length (bits.drop (count n * (seed n + 1)))

end ComplexityOfGenerators.Simulation.ExactRecursive
