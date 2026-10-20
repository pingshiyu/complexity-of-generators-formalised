import ComplexityOfGenerators.Simulation.ExactRecursive.WalkLoop
import ComplexityOfGenerators.Simulation.ExactRecursive.Base

namespace ComplexityOfGenerators.Simulation.ExactRecursive

open WordStack

variable {α : Type} [Fintype α] (B : Machine Unit Bool α) (V : Machine α α α)

noncomputable def algorithm (first : α)
    (baseSeed baseTime inverseSeed inverseTime count fuel : PolynomialBound) (n : ℕ) (bits : BitString) :
    Option (List α) :=
  (baseValue B baseTime n (bits.take (baseSeed n))).bind fun word =>
    walkResult V first count inverseSeed inverseTime n (fuel n) word (bits.drop (baseSeed n))

theorem body_correct (first : α)
    (baseSeed baseTime inverseSeed inverseTime count fuel : PolynomialBound) (n : ℕ)
    (bits : BitString) (s : Store B V)
    (input : s 11 = []) (auxiliary : s 12 = []) (index : (s 13).length = n)
    (random : s 17 = bits.map Symbol.bit) (empty : s 14 = []) (stopped : s 28 = [])
    (enough : baseSeed n + fuel n * (1 + count n * (inverseSeed n + 1)) ≤ bits.length) :
    ∃ state rest,
      WalkStored B V n state rest ((body B V first baseSeed baseTime inverseSeed inverseTime count fuel).eval s) ∧
      (body B V first baseSeed baseTime inverseSeed inverseTime count fuel).eval s 30 =
        flagWord B V (decide (state.word.length = n)) ∧
      state.answer n = algorithm B V first baseSeed baseTime inverseSeed inverseTime count fuel n bits := by
  let initial := baseState (baseValue B baseTime n (bits.take (baseSeed n)))
  let start := (baseFinish B V).eval ((baseTrial B V baseSeed baseTime).eval s)
  let counted := (counter B V 22 (by decide) fuel).eval start
  have base := baseTrial_view B V baseSeed baseTime n bits s input auxiliary index random empty stopped
  have clocked : WalkStored B V n initial (bits.drop (baseSeed n)) counted := by
    rcases base with ⟨hi, hn, hr, he, hv, hs⟩
    constructor <;> simp_all [counted, counter, CounterRoutine.routine_eval, start, initial]
  have count_eq : (counted 22).length = fuel n := by
    simp [counted, counter, CounterRoutine.routine_eval, show (start 13).length = n from base.index]
  have remaining : fuel n * (1 + count n * (inverseSeed n + 1)) ≤ (bits.drop (baseSeed n)).length := by
    simp only [List.length_drop]
    omega
  have walked := walkIter_correct B V first count inverseSeed inverseTime n (fuel n)
    (initial, bits.drop (baseSeed n)) counted clocked remaining
  obtain ⟨stored, target⟩ := walked.length_test
  have answer := walkIter_answer V first count inverseSeed inverseTime n (fuel n) initial
    (bits.drop (baseSeed n)) remaining
  refine ⟨((walkNext V first count inverseSeed inverseTime n)^[fuel n] (initial, bits.drop (baseSeed n))).1,
    ((walkNext V first count inverseSeed inverseTime n)^[fuel n] (initial, bits.drop (baseSeed n))).2, ?_, ?_, ?_⟩
  · change WalkStored B V n _ _ ((lengthTest B V).eval
      ((WordStack.Routine.counted 22 (walkStep B V first count inverseSeed inverseTime)).eval^[(counted 22).length] counted))
    rw [count_eq]
    exact stored
  · change (lengthTest B V).eval
      ((WordStack.Routine.counted 22 (walkStep B V first count inverseSeed inverseTime)).eval^[(counted 22).length] counted) 30 = _
    rw [count_eq]
    exact target
  · rw [answer]
    cases value : baseValue B baseTime n (bits.take (baseSeed n)) <;>
      simp [algorithm, initial, value, baseState, Walker.answer]

end ComplexityOfGenerators.Simulation.ExactRecursive
